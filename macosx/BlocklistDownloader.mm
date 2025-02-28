/******************************************************************************
 * Copyright (c) 2008-2012 Transmission authors and contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *****************************************************************************/

#import "BlocklistDownloader.h"
#import "BlocklistDownloaderViewController.h"
#import "BlocklistScheduler.h"
#import "Controller.h"

@interface BlocklistDownloader (Private)

- (void)startDownload;
- (void)decompressBlocklist;

@end

@implementation BlocklistDownloader

BlocklistDownloader* fBLDownloader = nil;

+ (BlocklistDownloader*)downloader
{
    if (!fBLDownloader)
    {
        fBLDownloader = [[BlocklistDownloader alloc] init];
        [fBLDownloader startDownload];
    }

    return fBLDownloader;
}

+ (BOOL)isRunning
{
    return fBLDownloader != nil;
}

- (void)setViewController:(BlocklistDownloaderViewController*)viewController
{
    fViewController = viewController;
    if (fViewController)
    {
        switch (fState)
        {
        case BLOCKLIST_DL_START:
            [fViewController setStatusStarting];
            break;
        case BLOCKLIST_DL_DOWNLOADING:
            [fViewController setStatusProgressForCurrentSize:fCurrentSize expectedSize:fExpectedSize];
            break;
        case BLOCKLIST_DL_PROCESSING:
            [fViewController setStatusProcessing];
            break;
        }
    }
}

- (void)cancelDownload
{
    [fViewController setFinished];

    [fDownload cancel];

    [BlocklistScheduler.scheduler updateSchedule];

    fBLDownloader = nil;
}

//using the actual filename is the best bet
- (void)download:(NSURLDownload*)download decideDestinationWithSuggestedFilename:(NSString*)filename
{
    [fDownload setDestination:[NSTemporaryDirectory() stringByAppendingPathComponent:filename] allowOverwrite:NO];
}

- (void)download:(NSURLDownload*)download didCreateDestination:(NSString*)path
{
    fDestination = path;
}

- (void)download:(NSURLDownload*)download didReceiveResponse:(NSURLResponse*)response
{
    fState = BLOCKLIST_DL_DOWNLOADING;

    fCurrentSize = 0;
    fExpectedSize = response.expectedContentLength;

    [fViewController setStatusProgressForCurrentSize:fCurrentSize expectedSize:fExpectedSize];
}

- (void)download:(NSURLDownload*)download didReceiveDataOfLength:(NSUInteger)length
{
    fCurrentSize += length;
    [fViewController setStatusProgressForCurrentSize:fCurrentSize expectedSize:fExpectedSize];
}

- (void)download:(NSURLDownload*)download didFailWithError:(NSError*)error
{
    [fViewController setFailed:error.localizedDescription];

    [NSUserDefaults.standardUserDefaults setObject:[NSDate date] forKey:@"BlocklistNewLastUpdate"];
    [BlocklistScheduler.scheduler updateSchedule];

    fBLDownloader = nil;
}

- (void)downloadDidFinish:(NSURLDownload*)download
{
    fState = BLOCKLIST_DL_PROCESSING;

    [fViewController setStatusProcessing];

    NSAssert(fDestination != nil, @"the blocklist file destination has not been specified");

    dispatch_async(dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0), ^{
        [self decompressBlocklist];

        dispatch_async(dispatch_get_main_queue(), ^{
            int const count = tr_blocklistSetContent(((Controller*)NSApp.delegate).sessionHandle, fDestination.UTF8String);

            //delete downloaded file
            [NSFileManager.defaultManager removeItemAtPath:fDestination error:NULL];

            if (count > 0)
            {
                [fViewController setFinished];
            }
            else
            {
                [fViewController setFailed:NSLocalizedString(@"The specified blocklist file did not contain any valid rules.", "blocklist fail message")];
            }

            //update last updated date for schedule
            NSDate* date = [NSDate date];
            [NSUserDefaults.standardUserDefaults setObject:date forKey:@"BlocklistNewLastUpdate"];
            [NSUserDefaults.standardUserDefaults setObject:date forKey:@"BlocklistNewLastUpdateSuccess"];
            [BlocklistScheduler.scheduler updateSchedule];

            [NSNotificationCenter.defaultCenter postNotificationName:@"BlocklistUpdated" object:nil];

            fBLDownloader = nil;
        });
    });
}

- (BOOL)download:(NSURLDownload*)download shouldDecodeSourceDataOfMIMEType:(NSString*)encodingType
{
    return YES;
}

@end

@implementation BlocklistDownloader (Private)

- (void)startDownload
{
    fState = BLOCKLIST_DL_START;

    [BlocklistScheduler.scheduler cancelSchedule];

    NSString* urlString = [NSUserDefaults.standardUserDefaults stringForKey:@"BlocklistURL"];
    if (!urlString)
    {
        urlString = @"";
    }
    else if (![urlString isEqualToString:@""] && [urlString rangeOfString:@"://"].location == NSNotFound)
    {
        urlString = [@"http://" stringByAppendingString:urlString];
    }

    NSURLRequest* request = [NSURLRequest requestWithURL:[NSURL URLWithString:urlString]];

    fDownload = [[NSURLDownload alloc] initWithRequest:request delegate:self];
}

//.gz, .tar.gz, .tgz, and .bgz will be decompressed by NSURLDownload for us. However, we have to do .zip files manually.
- (void)decompressBlocklist
{
    if ([fDestination.pathExtension.lowercaseString isEqualToString:@"zip"])
    {
        BOOL success = NO;

        NSString* workingDirectory = fDestination.stringByDeletingLastPathComponent;

        //First, perform the actual unzipping
        NSTask* unzip = [[NSTask alloc] init];
        unzip.launchPath = @"/usr/bin/unzip";
        unzip.currentDirectoryPath = workingDirectory;
        unzip.arguments = @[
            @"-o", /* overwrite */
            @"-q", /* quiet! */
            fDestination, /* source zip file */
            @"-d",
            workingDirectory /*destination*/
        ];

        @try
        {
            [unzip launch];
            [unzip waitUntilExit];

            if (unzip.terminationStatus == 0)
            {
                success = YES;
            }
        }
        @catch (id exc)
        {
            success = NO;
        }

        if (success)
        {
            //Now find out what file we actually extracted; don't just assume it matches the zipfile's name
            NSTask* zipinfo;

            zipinfo = [[NSTask alloc] init];
            zipinfo.launchPath = @"/usr/bin/zipinfo";
            zipinfo.arguments = @[
                @"-1", /* just the filename */
                fDestination /* source zip file */
            ];
            zipinfo.standardOutput = [NSPipe pipe];

            @try
            {
                NSFileHandle* zipinfoOutput = [zipinfo.standardOutput fileHandleForReading];

                [zipinfo launch];
                [zipinfo waitUntilExit];

                NSString* actualFilename = [[NSString alloc] initWithData:[zipinfoOutput readDataToEndOfFile]
                                                                 encoding:NSUTF8StringEncoding];
                actualFilename = [actualFilename stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
                NSString* newBlocklistPath = [workingDirectory stringByAppendingPathComponent:actualFilename];

                //Finally, delete the ZIP file; we're done with it, and we'll return the unzipped blocklist
                [NSFileManager.defaultManager removeItemAtPath:fDestination error:NULL];

                fDestination = newBlocklistPath;
            }
            @catch (id exc)
            {
            }
        }
    }
}

@end

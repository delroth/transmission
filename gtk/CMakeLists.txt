project(trgtk)

add_compile_options(${C_WARNING_FLAGS})

if(WITH_LIBAPPINDICATOR)
    add_definitions(-DHAVE_LIBAPPINDICATOR)
endif()

execute_process(
    COMMAND
        ${PKG_CONFIG_EXECUTABLE} gio-2.0 --variable glib_compile_resources
    OUTPUT_VARIABLE
        GLIB_COMPILE_RESOURCES_EXECUTABLE
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

if(NOT GLIB_COMPILE_RESOURCES_EXECUTABLE)
    message(SEND_ERROR "Unable to find glib-compile-resources executable")
endif()

add_custom_command(
    OUTPUT
        ${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.c
        ${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.h
    COMMAND
        ${GLIB_COMPILE_RESOURCES_EXECUTABLE}
        --target=${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.c
        --sourcedir=${CMAKE_CURRENT_SOURCE_DIR}
        --generate-source
        --c-name transmission
        transmission.gresource.xml
    COMMAND
        ${GLIB_COMPILE_RESOURCES_EXECUTABLE}
        --target=${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.h
        --sourcedir=${CMAKE_CURRENT_SOURCE_DIR}
        --generate-header
        --c-name transmission
        transmission.gresource.xml
    DEPENDS
        icons/hicolor_apps_scalable_transmission.svg
        icons/lock.png
        icons/ratio.png
        icons/turtle-blue.png
        icons/turtle-grey.png
        icons/utilities.png
        transmission.gresource.xml
        transmission-ui.xml
    WORKING_DIRECTORY
        ${CMAKE_CURRENT_SOURCE_DIR}
)

if(ENABLE_NLS)
    set(${PROJECT_NAME}_DESKTOP_FILE "${PROJECT_BINARY_DIR}/${TR_NAME}-gtk.desktop")
    add_custom_command(
        OUTPUT ${${PROJECT_NAME}_DESKTOP_FILE}
        COMMAND ${GETTEXT_MSGFMT_EXECUTABLE} --desktop -d ${CMAKE_SOURCE_DIR}/po --template ${PROJECT_SOURCE_DIR}/transmission-gtk.desktop.in -o ${${PROJECT_NAME}_DESKTOP_FILE}
        DEPENDS ${PROJECT_SOURCE_DIR}/transmission-gtk.desktop.in
        VERBATIM
    )

    set(${PROJECT_NAME}_APPDATA_FILE "${PROJECT_BINARY_DIR}/${TR_NAME}-gtk.appdata.xml")
    add_custom_command(
        OUTPUT ${${PROJECT_NAME}_APPDATA_FILE}
        COMMAND ${GETTEXT_MSGFMT_EXECUTABLE} --xml -d ${CMAKE_SOURCE_DIR}/po --template ${PROJECT_SOURCE_DIR}/transmission-gtk.appdata.xml.in -o ${${PROJECT_NAME}_APPDATA_FILE}
        DEPENDS ${PROJECT_SOURCE_DIR}/transmission-gtk.appdata.xml.in
        VERBATIM
    )
endif()

set(${PROJECT_NAME}_SOURCES
    actions.cc
    conf.cc
    details.cc
    dialogs.cc
    favicon.cc
    file-list.cc
    filter.cc
    hig.cc
    icons.cc
    main.cc
    makemeta-ui.cc
    msgwin.cc
    notify.cc
    open-dialog.cc
    relocate.cc
    stats.cc
    torrent-cell-renderer.cc
    tr-core.cc
    tr-icon.cc
    tr-prefs.cc
    tr-window.cc
    util.cc
    ${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.c
)

set(${PROJECT_NAME}_HEADERS
    actions.h
    conf.h
    details.h
    dialogs.h
    favicon.h
    file-list.h
    filter.h
    hig.h
    icons.h
    makemeta-ui.h
    msgwin.h
    notify.h
    open-dialog.h
    relocate.h
    stats.h
    torrent-cell-renderer.h
    tr-core.h
    tr-icon.h
    tr-prefs.h
    tr-window.h
    util.h
    ${CMAKE_CURRENT_BINARY_DIR}/transmission-resources.h
)

include_directories(
    ${CMAKE_SOURCE_DIR}
    ${PROJECT_BINARY_DIR}
)
include_directories(
    SYSTEM
    ${LIBAPPINDICATOR_INCLUDE_DIRS}
    ${GTK_INCLUDE_DIRS}
    ${CURL_INCLUDE_DIRS}
    ${EVENT2_INCLUDE_DIRS}
)

link_directories(
    ${GTK_LIBRARY_DIRS}
)

add_definitions(
    "-DTRANSMISSIONLOCALEDIR=\"${CMAKE_INSTALL_FULL_LOCALEDIR}\""
    "-DGETTEXT_PACKAGE=\"${TR_NAME}-gtk\""
    -DG_DISABLE_DEPRECATED
    -DGDK_PIXBUF_DISABLE_DEPRECATED
    -DGDK_DISABLE_DEPRECATED
    # FIXME: migrate from GtkUIManager to GtkBuilder in 2.90
    # -DGTK_DISABLE_DEPRECATED
    -DPANGO_DISABLE_DEPRECATED
    # FIXME: these break libnotify's headers
    # -DG_DISABLE_SINGLE_INCLUDES
    # -DGTK_DISABLE_SINGLE_INCLUDES
    ${GTK_CFLAGS_OTHER}
)

tr_win32_app_info(${PROJECT_NAME}_WIN32_RC_FILE
    "Transmission GTK+ Client"
    "${TR_NAME}-gtk"
    "${TR_NAME}-gtk.exe"
    "${TR_NAME}.ico")

add_executable(${TR_NAME}-gtk WIN32
    ${${PROJECT_NAME}_SOURCES}
    ${${PROJECT_NAME}_HEADERS}
    ${${PROJECT_NAME}_DESKTOP_FILE}
    ${${PROJECT_NAME}_APPDATA_FILE}
    ${${PROJECT_NAME}_WIN32_RC_FILE}
)

target_link_libraries(${TR_NAME}-gtk
    ${TR_NAME}
    ${LIBAPPINDICATOR_LIBRARIES}
    ${GTK_LIBRARIES}
    ${CURL_LIBRARIES}
    ${EVENT2_LIBRARIES}
)

if(NOT MSVC)
    # https://github.com/transmission/transmission/issues/1381 patches welcome
    target_compile_options(${TR_NAME}-gtk PRIVATE -Wno-deprecated-declarations)
endif()

if(MSVC)
    tr_append_target_property(${TR_NAME}-gtk LINK_FLAGS "/ENTRY:mainCRTStartup")
endif()

install(TARGETS ${TR_NAME}-gtk DESTINATION ${CMAKE_INSTALL_BINDIR})

set(${PROJECT_NAME}_PUBLIC_ICONS
    hicolor_apps_scalable_transmission.svg
    hicolor_apps_scalable_transmission-devel.svg
    hicolor_apps_symbolic_transmission-symbolic.svg
)

set(ICON_NAME_REGEX "^([^_]+)_([^_]+)_([^_]+)_(.+)$")
foreach(ICON ${${PROJECT_NAME}_PUBLIC_ICONS})
    string(REGEX REPLACE ${ICON_NAME_REGEX} "\\1/\\3/\\2" ICON_DIR ${ICON})
    string(REGEX REPLACE ${ICON_NAME_REGEX} "\\4" ICON_NAME ${ICON})
    install(FILES icons/${ICON} DESTINATION ${CMAKE_INSTALL_DATADIR}/icons/${ICON_DIR}/ RENAME ${ICON_NAME})
endforeach()

if(INSTALL_DOC)
    install(FILES ${TR_NAME}-gtk.1 DESTINATION ${CMAKE_INSTALL_MANDIR}/man1)
endif()

if(ENABLE_NLS)
    install(FILES ${${PROJECT_NAME}_DESKTOP_FILE} DESTINATION ${CMAKE_INSTALL_DATADIR}/applications)
    install(FILES ${${PROJECT_NAME}_APPDATA_FILE} DESTINATION ${CMAKE_INSTALL_DATADIR}/appdata)
else()
    install(FILES transmission-gtk.desktop.in DESTINATION ${CMAKE_INSTALL_DATADIR}/applications RENAME ${TR_NAME}-gtk.desktop)
endif()

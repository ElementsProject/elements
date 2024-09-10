ifneq ($(shell $(SHELL) $(.SHELLFLAGS) "command -v $(host)-g++-posix"),)
mingw32_CXX := $(host)-g++-posix
endif

mingw32_CFLAGS=-pipe -std=$(C_STANDARD)
mingw32_CXXFLAGS=-pipe -std=$(CXX_STANDARD)

ifneq ($(LTO),)
mingw32_CFLAGS += -flto
mingw32_CXXFLAGS += -flto
mingw32_LDFLAGS += -flto
endif

mingw32_release_CFLAGS=-O2
mingw32_release_CXXFLAGS=$(mingw32_release_CFLAGS)

mingw32_debug_CFLAGS=-O1
mingw32_debug_CXXFLAGS=$(mingw32_debug_CFLAGS)

mingw32_debug_CPPFLAGS=-D_GLIBCXX_DEBUG -D_GLIBCXX_DEBUG_PEDANTIC

mingw32_cmake_system=Windows

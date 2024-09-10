ifeq ($(HOST),armv7a-linux-android)
android_CXX=$(ANDROID_TOOLCHAIN_BIN)/$(HOST)eabi$(ANDROID_API_LEVEL)-clang++
android_CC=$(ANDROID_TOOLCHAIN_BIN)/$(HOST)eabi$(ANDROID_API_LEVEL)-clang
else
android_CXX=$(ANDROID_TOOLCHAIN_BIN)/$(HOST)$(ANDROID_API_LEVEL)-clang++
android_CC=$(ANDROID_TOOLCHAIN_BIN)/$(HOST)$(ANDROID_API_LEVEL)-clang
endif

ifneq ($(LTO),)
android_CFLAGS += -flto
android_LDFLAGS += -flto
endif

android_AR=$(ANDROID_TOOLCHAIN_BIN)/llvm-ar
android_RANLIB=$(ANDROID_TOOLCHAIN_BIN)/llvm-ranlib

android_cmake_system=Android

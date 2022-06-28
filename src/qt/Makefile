.PHONY: FORCE
all: FORCE
	$(MAKE) -C .. elements_qt test_elements_qt
clean: FORCE
	$(MAKE) -C .. elements_qt_clean test_elements_qt_clean
check: FORCE
	$(MAKE) -C .. test_elements_qt_check
elements-qt elements-qt.exe: FORCE
	 $(MAKE) -C .. elements_qt
apk: FORCE
	$(MAKE) -C .. elements_qt_apk

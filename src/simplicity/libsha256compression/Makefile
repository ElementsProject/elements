CFLAGS := -I include -fPIC -Werror -Wall -Wextra -Wcast-qual -Wcast-align -Wstrict-aliasing -Wpointer-arith -Winit-self -Wshadow -Wswitch-enum -Wstrict-prototypes -Wmissing-prototypes -Wredundant-decls -Wfloat-equal -Wundef -Wconversion

libsha256compression.so: sha256/compression.o
	$(CC) $(CFLAGS) -shared $^ -o $@

install: libsha256compression.so
	mkdir -p $(out)/lib
	cp $^ $(out)/lib/
	cp -r include $(out)/

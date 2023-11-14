OBJS := bitstream.o dag.o deserialize.o eval.o frame.o jets.o jets-secp256k1.o rsort.o sha256.o type.o typeInference.o primitive/elements/env.o primitive/elements/exec.o primitive/elements/ops.o primitive/elements/jets.o primitive/elements/primitive.o
TEST_OBJS := test.o ctx8Pruned.o ctx8Unpruned.o hashBlock.o schnorr0.o schnorr6.o primitive/elements/checkSigHashAllTx1.o

# From https://fastcompression.blogspot.com/2019/01/compiler-warnings.html
CWARN := -Werror -Wall -Wextra -Wcast-qual -Wcast-align -Wstrict-aliasing -Wpointer-arith -Winit-self -Wshadow -Wswitch-enum -Wstrict-prototypes -Wmissing-prototypes -Wredundant-decls -Wfloat-equal -Wundef -Wconversion

ifneq ($(doCheck), 1)
CPPFLAGS := $(CPPFLAGS) -DPRODUCTION
endif

CFLAGS := $(CFLAGS) -I include

# libsecp256k1 is full of conversion warnings, so we compile jets-secp256k1.c separately.
jets-secp256k1.o: jets-secp256k1.c
	$(CC) -c $(CFLAGS) $(CWARN) -Wno-conversion $(CPPFLAGS) -o $@ $<

primitive/elements/jets.o: primitive/elements/jets.c
	$(CC) -c $(CFLAGS) $(CWARN) -Wno-switch-enum -Wswitch $(CPPFLAGS) -o $@ $<

%.o: %.c
	$(CC) -c $(CFLAGS) $(CWARN) $(CPPFLAGS) -o $@ $<

libElementsSimplicity.a: $(OBJS)
	ar rcs $@ $^

test: $(TEST_OBJS) libElementsSimplicity.a
	$(CC) $^ -o $@ $(LDFLAGS)

install: libElementsSimplicity.a
	mkdir -p $(out)/lib
	cp $^ $(out)/lib/
	cp -R include $(out)/include

check: test
	./test

clean:
	-rm -f test libElementsSimplicity.a $(TEST_OBJS) $(OBJS)

.PHONY: install check clean

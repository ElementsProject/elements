(use-modules (gnu)
             (gnu packages)
             (gnu packages autotools)
             (gnu packages base)
             (gnu packages bash)
             (gnu packages bison)
             (gnu packages certs)
             (gnu packages cdrom)
             (gnu packages check)
             (gnu packages cmake)
             (gnu packages commencement)
             (gnu packages compression)
             (gnu packages cross-base)
             (gnu packages curl)
             (gnu packages file)
             (gnu packages gawk)
             (gnu packages gcc)
             (gnu packages gnome)
             (gnu packages installers)
             (gnu packages linux)
             (gnu packages llvm)
             (gnu packages mingw)
             (gnu packages moreutils)
             (gnu packages perl)
             (gnu packages pkg-config)
             (gnu packages python)
             (gnu packages python-crypto)
             (gnu packages python-web)
             (gnu packages shells)
             (gnu packages tls)
             (gnu packages version-control)
             (guix build-system gnu)
             (guix build-system python)
             (guix build-system trivial)
             (guix download)
             (guix gexp)
             (guix git-download)
             ((guix licenses) #:prefix license:)
             (guix packages)
             (guix profiles)
             (guix utils))

(define-syntax-rule (search-our-patches file-name ...)
  "Return the list of absolute file names corresponding to each
FILE-NAME found in ./patches relative to the current file."
  (parameterize
      ((%patch-path (list (string-append (dirname (current-filename)) "/patches"))))
    (list (search-patch file-name) ...)))

(define (make-ssp-fixed-gcc xgcc)
  "Given a XGCC package, return a modified package that uses the SSP function
from glibc instead of from libssp.so. Our `symbol-check' script will complain if
we link against libssp.so, and thus will ensure that this works properly.

Taken from:
http://www.linuxfromscratch.org/hlfs/view/development/chapter05/gcc-pass1.html"
  (package
    (inherit xgcc)
    (arguments
     (substitute-keyword-arguments (package-arguments xgcc)
       ((#:make-flags flags)
        `(cons "gcc_cv_libc_provides_ssp=yes" ,flags))))))

(define (make-gcc-rpath-link xgcc)
  "Given a XGCC package, return a modified package that replace each instance of
-rpath in the default system spec that's inserted by Guix with -rpath-link"
  (package
    (inherit xgcc)
    (arguments
     (substitute-keyword-arguments (package-arguments xgcc)
       ((#:phases phases)
        `(modify-phases ,phases
           (add-after 'pre-configure 'replace-rpath-with-rpath-link
             (lambda _
               (substitute* (cons "gcc/config/rs6000/sysv4.h"
                                  (find-files "gcc/config"
                                              "^gnu-user.*\\.h$"))
                 (("-rpath=") "-rpath-link="))
               #t))))))))

(define (make-cross-toolchain target
                              base-gcc-for-libc
                              base-kernel-headers
                              base-libc
                              base-gcc)
  "Create a cross-compilation toolchain package for TARGET"
  (let* ((xbinutils (cross-binutils target))
         ;; 1. Build a cross-compiling gcc without targeting any libc, derived
         ;; from BASE-GCC-FOR-LIBC
         (xgcc-sans-libc (cross-gcc target
                                    #:xgcc base-gcc-for-libc
                                    #:xbinutils xbinutils))
         ;; 2. Build cross-compiled kernel headers with XGCC-SANS-LIBC, derived
         ;; from BASE-KERNEL-HEADERS
         (xkernel (cross-kernel-headers target
                                        base-kernel-headers
                                        xgcc-sans-libc
                                        xbinutils))
         ;; 3. Build a cross-compiled libc with XGCC-SANS-LIBC and XKERNEL,
         ;; derived from BASE-LIBC
         (xlibc (cross-libc target
                            base-libc
                            xgcc-sans-libc
                            xbinutils
                            xkernel))
         ;; 4. Build a cross-compiling gcc targeting XLIBC, derived from
         ;; BASE-GCC
         (xgcc (cross-gcc target
                          #:xgcc base-gcc
                          #:xbinutils xbinutils
                          #:libc xlibc)))
    ;; Define a meta-package that propagates the resulting XBINUTILS, XLIBC, and
    ;; XGCC
    (package
      (name (string-append target "-toolchain"))
      (version (package-version xgcc))
      (source #f)
      (build-system trivial-build-system)
      (arguments '(#:builder (begin (mkdir %output) #t)))
      (propagated-inputs
       `(("binutils" ,xbinutils)
         ("libc" ,xlibc)
         ("libc:static" ,xlibc "static")
         ("gcc" ,xgcc)
         ("gcc-lib" ,xgcc "lib")))
      (synopsis (string-append "Complete GCC tool chain for " target))
      (description (string-append "This package provides a complete GCC tool
chain for " target " development."))
      (home-page (package-home-page xgcc))
      (license (package-license xgcc)))))

(define base-gcc gcc-10)
(define base-linux-kernel-headers linux-libre-headers-5.15)

;; Building glibc with stack smashing protector first landed in glibc 2.25, use
;; this function to disable for older glibcs
;;
;; From glibc 2.25 changelog:
;;
;;   * Most of glibc can now be built with the stack smashing protector enabled.
;;     It is recommended to build glibc with --enable-stack-protector=strong.
;;     Implemented by Nick Alcock (Oracle).
(define (make-glibc-without-ssp xglibc)
  (package-with-extra-configure-variable
   (package-with-extra-configure-variable
    xglibc "libc_cv_ssp" "no")
   "libc_cv_ssp_strong" "no"))

(define* (make-bitcoin-cross-toolchain target
                                       #:key
                                       (base-gcc-for-libc base-gcc)
                                       (base-kernel-headers base-linux-kernel-headers)
                                       (base-libc (make-glibc-without-ssp (make-glibc-without-werror glibc-2.24)))
                                       (base-gcc (make-gcc-rpath-link base-gcc)))
  "Convenience wrapper around MAKE-CROSS-TOOLCHAIN with default values
desirable for building Bitcoin Core release binaries."
  (make-cross-toolchain target
                        base-gcc-for-libc
                        base-kernel-headers
                        base-libc
                        base-gcc))

(define (make-gcc-with-pthreads gcc)
  (package-with-extra-configure-variable gcc "--enable-threads" "posix"))

(define (make-mingw-w64-cross-gcc cross-gcc)
  (package-with-extra-patches cross-gcc
    (search-our-patches "vmov-alignment.patch"
                        "gcc-broken-longjmp.patch")))

(define (make-mingw-pthreads-cross-toolchain target)
  "Create a cross-compilation toolchain package for TARGET"
  (let* ((xbinutils (cross-binutils target))
         (pthreads-xlibc mingw-w64-x86_64-winpthreads)
         (pthreads-xgcc (make-gcc-with-pthreads
                         (cross-gcc target
                                    #:xgcc (make-ssp-fixed-gcc (make-mingw-w64-cross-gcc base-gcc))
                                    #:xbinutils xbinutils
                                    #:libc pthreads-xlibc))))
    ;; Define a meta-package that propagates the resulting XBINUTILS, XLIBC, and
    ;; XGCC
    (package
      (name (string-append target "-posix-toolchain"))
      (version (package-version pthreads-xgcc))
      (source #f)
      (build-system trivial-build-system)
      (arguments '(#:builder (begin (mkdir %output) #t)))
      (propagated-inputs
       `(("binutils" ,xbinutils)
         ("libc" ,pthreads-xlibc)
         ("gcc" ,pthreads-xgcc)
         ("gcc-lib" ,pthreads-xgcc "lib")))
      (synopsis (string-append "Complete GCC tool chain for " target))
      (description (string-append "This package provides a complete GCC tool
chain for " target " development."))
      (home-page (package-home-page pthreads-xgcc))
      (license (package-license pthreads-xgcc)))))

(define (make-nsis-for-gcc-10 base-nsis)
  (package-with-extra-patches base-nsis
    (search-our-patches "nsis-gcc-10-memmove.patch")))

(define-public lief
  (package
   (name "python-lief")
   (version "0.12.0")
   (source
    (origin
     (method git-fetch)
     (uri (git-reference
           (url "https://github.com/lief-project/LIEF.git")
           (commit version)))
     (file-name (git-file-name name version))
     (sha256
      (base32
       "026jchj56q25v6gc0754dj9cj5hz5zaza8ij93y5ga94w20kzm9q"))))
   (build-system python-build-system)
   (native-inputs
    `(("cmake" ,cmake)))
   (home-page "https://github.com/lief-project/LIEF")
   (synopsis "Library to Instrument Executable Formats")
   (description "Python library to to provide a cross platform library which can
parse, modify and abstract ELF, PE and MachO formats.")
   (license license:asl2.0)))

(define osslsigncode
  (package
    (name "osslsigncode")
    (version "2.0")
    (source (origin
              (method url-fetch)
              (uri (string-append "https://github.com/mtrojnar/"
                                  name "/archive/" version ".tar.gz"))
              (sha256
               (base32
                "0byri6xny770wwb2nciq44j5071122l14bvv65axdd70nfjf0q2s"))))
    (build-system gnu-build-system)
    (native-inputs
     `(("pkg-config" ,pkg-config)
       ("autoconf" ,autoconf)
       ("automake" ,automake)
       ("libtool" ,libtool)))
    (inputs
     `(("openssl" ,openssl)))
    (arguments
     `(#:configure-flags
       `("--without-gsf"
         "--without-curl"
         "--disable-dependency-tracking")))
    (home-page "https://github.com/mtrojnar/osslsigncode")
    (synopsis "Authenticode signing and timestamping tool")
    (description "osslsigncode is a small tool that implements part of the
functionality of the Microsoft tool signtool.exe - more exactly the Authenticode
signing and timestamping. But osslsigncode is based on OpenSSL and cURL, and
thus should be able to compile on most platforms where these exist.")
    (license license:gpl3+))) ; license is with openssl exception

(define-public python-elfesteem
  (let ((commit "87bbd79ab7e361004c98cc8601d4e5f029fd8bd5"))
    (package
      (name "python-elfesteem")
      (version (git-version "0.1" "1" commit))
      (source
       (origin
         (method git-fetch)
         (uri (git-reference
               (url "https://github.com/LRGH/elfesteem")
               (commit commit)))
         (file-name (git-file-name name commit))
         (sha256
          (base32
           "1nyvjisvyxyxnd0023xjf5846xd03lwawp5pfzr8vrky7wwm5maz"))
      (patches (search-our-patches "elfsteem-value-error-python-39.patch"))))
      (build-system python-build-system)
      ;; There are no tests, but attempting to run python setup.py test leads to
      ;; PYTHONPATH problems, just disable the test
      (arguments '(#:tests? #f))
      (home-page "https://github.com/LRGH/elfesteem")
      (synopsis "ELF/PE/Mach-O parsing library")
      (description "elfesteem parses ELF, PE and Mach-O files.")
      (license license:lgpl2.1))))

(define-public python-oscrypto
  (package
    (name "python-oscrypto")
    (version "1.2.1")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/wbond/oscrypto")
             (commit version)))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "1d4d8s4z340qhvb3g5m5v3436y3a71yc26wk4749q64m09kxqc3l"))
       (patches (search-our-patches "oscrypto-hard-code-openssl.patch"))))
    (build-system python-build-system)
    (native-search-paths
     (list (search-path-specification
            (variable "SSL_CERT_FILE")
            (file-type 'regular)
            (separator #f)                ;single entry
            (files '("etc/ssl/certs/ca-certificates.crt")))))

    (propagated-inputs
     `(("python-asn1crypto" ,python-asn1crypto)
       ("openssl" ,openssl)))
    (arguments
     `(#:phases
       (modify-phases %standard-phases
         (add-after 'unpack 'hard-code-path-to-libscrypt
           (lambda* (#:key inputs #:allow-other-keys)
             (let ((openssl (assoc-ref inputs "openssl")))
               (substitute* "oscrypto/__init__.py"
                 (("@GUIX_OSCRYPTO_USE_OPENSSL@")
                  (string-append openssl "/lib/libcrypto.so" "," openssl "/lib/libssl.so")))
               #t)))
         (add-after 'unpack 'disable-broken-tests
           (lambda _
             ;; This test is broken as there is no keyboard interrupt.
             (substitute* "tests/test_trust_list.py"
               (("^(.*)class TrustListTests" line indent)
                (string-append indent
                               "@unittest.skip(\"Disabled by Guix\")\n"
                               line)))
             (substitute* "tests/test_tls.py"
               (("^(.*)class TLSTests" line indent)
                (string-append indent
                               "@unittest.skip(\"Disabled by Guix\")\n"
                               line)))
             #t))
         (replace 'check
           (lambda _
             (invoke "python" "run.py" "tests")
             #t)))))
    (home-page "https://github.com/wbond/oscrypto")
    (synopsis "Compiler-free Python crypto library backed by the OS")
    (description "oscrypto is a compilation-free, always up-to-date encryption library for Python.")
    (license license:expat)))

(define-public python-oscryptotests
  (package (inherit python-oscrypto)
    (name "python-oscryptotests")
    (propagated-inputs
      `(("python-oscrypto" ,python-oscrypto)))
    (arguments
     `(#:tests? #f
       #:phases
       (modify-phases %standard-phases
         (add-after 'unpack 'hard-code-path-to-libscrypt
           (lambda* (#:key inputs #:allow-other-keys)
             (chdir "tests")
             #t)))))))

(define-public python-certvalidator
  (let ((commit "a145bf25eb75a9f014b3e7678826132efbba6213"))
    (package
      (name "python-certvalidator")
      (version (git-version "0.1" "1" commit))
      (source
       (origin
         (method git-fetch)
         (uri (git-reference
               (url "https://github.com/achow101/certvalidator")
               (commit commit)))
         (file-name (git-file-name name commit))
         (sha256
          (base32
           "1qw2k7xis53179lpqdqyylbcmp76lj7sagp883wmxg5i7chhc96k"))))
      (build-system python-build-system)
      (propagated-inputs
       `(("python-asn1crypto" ,python-asn1crypto)
         ("python-oscrypto" ,python-oscrypto)
         ("python-oscryptotests", python-oscryptotests))) ;; certvalidator tests import oscryptotests
      (arguments
       `(#:phases
         (modify-phases %standard-phases
           (add-after 'unpack 'disable-broken-tests
             (lambda _
               (substitute* "tests/test_certificate_validator.py"
                 (("^(.*)class CertificateValidatorTests" line indent)
                  (string-append indent
                                 "@unittest.skip(\"Disabled by Guix\")\n"
                                 line)))
               (substitute* "tests/test_crl_client.py"
                 (("^(.*)def test_fetch_crl" line indent)
                  (string-append indent
                                 "@unittest.skip(\"Disabled by Guix\")\n"
                                 line)))
               (substitute* "tests/test_ocsp_client.py"
                 (("^(.*)def test_fetch_ocsp" line indent)
                  (string-append indent
                                 "@unittest.skip(\"Disabled by Guix\")\n"
                                 line)))
               (substitute* "tests/test_registry.py"
                 (("^(.*)def test_build_paths" line indent)
                  (string-append indent
                                 "@unittest.skip(\"Disabled by Guix\")\n"
                                 line)))
               (substitute* "tests/test_validate.py"
                 (("^(.*)def test_revocation_mode_hard" line indent)
                  (string-append indent
                                 "@unittest.skip(\"Disabled by Guix\")\n"
                                 line)))
               #t))
           (replace 'check
             (lambda _
               (invoke "python" "run.py" "tests")
               #t)))))
      (home-page "https://github.com/wbond/certvalidator")
      (synopsis "Python library for validating X.509 certificates and paths")
      (description "certvalidator is a Python library for validating X.509
certificates or paths. Supports various options, including: validation at a
specific moment in time, whitelisting and revocation checks.")
      (license license:expat))))

(define-public python-altgraph
  (package
    (name "python-altgraph")
    (version "0.17")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/ronaldoussoren/altgraph")
             (commit (string-append "v" version))))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "09sm4srvvkw458pn48ga9q7ykr4xlz7q8gh1h9w7nxpf001qgpwb"))))
    (build-system python-build-system)
    (home-page "https://github.com/ronaldoussoren/altgraph")
    (synopsis "Python graph (network) package")
    (description "altgraph is a fork of graphlib: a graph (network) package for
constructing graphs, BFS and DFS traversals, topological sort, shortest paths,
etc. with graphviz output.")
    (license license:expat)))


(define-public python-macholib
  (package
    (name "python-macholib")
    (version "1.14")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/ronaldoussoren/macholib")
             (commit (string-append "v" version))))
       (file-name (git-file-name name version))
       (sha256
        (base32
         "0aislnnfsza9wl4f0vp45ivzlc0pzhp9d4r08700slrypn5flg42"))))
    (build-system python-build-system)
    (propagated-inputs
     `(("python-altgraph" ,python-altgraph)))
    (arguments
     '(#:phases
       (modify-phases %standard-phases
         (add-after 'unpack 'disable-broken-tests
           (lambda _
             ;; This test is broken as there is no keyboard interrupt.
             (substitute* "macholib_tests/test_command_line.py"
               (("^(.*)class TestCmdLine" line indent)
                (string-append indent
                               "@unittest.skip(\"Disabled by Guix\")\n"
                               line)))
             (substitute* "macholib_tests/test_dyld.py"
               (("^(.*)def test_\\S+_find" line indent)
                (string-append indent
                               "@unittest.skip(\"Disabled by Guix\")\n"
                               line))
               (("^(.*)def testBasic" line indent)
                (string-append indent
                               "@unittest.skip(\"Disabled by Guix\")\n"
                               line))
               )
             #t)))))
    (home-page "https://github.com/ronaldoussoren/macholib")
    (synopsis "Python library for analyzing and editing Mach-O headers")
    (description "macholib is a Macho-O header analyzer and editor. It's
typically used as a dependency analysis tool, and also to rewrite dylib
references in Mach-O headers to be @executable_path relative. Though this tool
targets a platform specific file format, it is pure python code that is platform
and endian independent.")
    (license license:expat)))

(define-public python-signapple
  (let ((commit "8a945a2e7583be2665cf3a6a89d665b70ecd1ab6"))
    (package
      (name "python-signapple")
      (version (git-version "0.1" "1" commit))
      (source
       (origin
         (method git-fetch)
         (uri (git-reference
               (url "https://github.com/achow101/signapple")
               (commit commit)))
         (file-name (git-file-name name commit))
         (sha256
          (base32
           "0fr1hangvfyiwflca6jg5g8zvg3jc9qr7vd2c12ff89pznf38dlg"))))
      (build-system python-build-system)
      (propagated-inputs
       `(("python-asn1crypto" ,python-asn1crypto)
         ("python-oscrypto" ,python-oscrypto)
         ("python-certvalidator" ,python-certvalidator)
         ("python-elfesteem" ,python-elfesteem)
         ("python-requests" ,python-requests)
         ("python-macholib" ,python-macholib)))
      ;; There are no tests, but attempting to run python setup.py test leads to
      ;; problems, just disable the test
      (arguments '(#:tests? #f))
      (home-page "https://github.com/achow101/signapple")
      (synopsis "Mach-O binary signature tool")
      (description "signapple is a Python tool for creating, verifying, and
inspecting signatures in Mach-O binaries.")
      (license license:expat))))

(define (make-glibc-without-werror glibc)
  (package-with-extra-configure-variable glibc "enable_werror" "no"))

(define-public glibc-2.24
  (package
    (inherit glibc-2.31)
    (version "2.24")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://sourceware.org/git/glibc.git")
                    (commit "0d7f1ed30969886c8dde62fbf7d2c79967d4bace")))
              (file-name (git-file-name "glibc" "0d7f1ed30969886c8dde62fbf7d2c79967d4bace"))
              (sha256
               (base32
                "0g5hryia5v1k0qx97qffgwzrz4lr4jw3s5kj04yllhswsxyjbic3"))
              (patches (search-our-patches "glibc-ldd-x86_64.patch"
                                           "glibc-versioned-locpath.patch"
                                           "glibc-2.24-elfm-loadaddr-dynamic-rewrite.patch"
                                           "glibc-2.24-no-build-time-cxx-header-run.patch"
                                           "glibc-2.24-fcommon.patch"))))))

(define-public glibc-2.27/bitcoin-patched
  (package
    (inherit glibc-2.31)
    (version "2.27")
    (source (origin
              (method git-fetch)
              (uri (git-reference
                    (url "https://sourceware.org/git/glibc.git")
                    (commit "23158b08a0908f381459f273a984c6fd328363cb")))
              (file-name (git-file-name "glibc" "23158b08a0908f381459f273a984c6fd328363cb"))
              (sha256
               (base32
                "1b2n1gxv9f4fd5yy68qjbnarhf8mf4vmlxk10i3328c1w5pmp0ca"))
              (patches (search-our-patches "glibc-ldd-x86_64.patch"
                                           "glibc-2.27-riscv64-Use-__has_include-to-include-asm-syscalls.h.patch"
                                           "glibc-2.27-dont-redefine-nss-database.patch"))))))

(packages->manifest
 (append
  (list ;; The Basics
        bash
        which
        coreutils
        util-linux
        ;; File(system) inspection
        file
        grep
        diffutils
        findutils
        ;; File transformation
        patch
        gawk
        sed
        moreutils
        ;; Compression and archiving
        tar
        bzip2
        gzip
        xz
        ;; Build tools
        gnu-make
        libtool-2.4.7
        autoconf-2.71
        automake
        pkg-config
        bison
        ;; Native GCC 10 toolchain
        gcc-toolchain-10
        (list gcc-toolchain-10 "static")
        ;; Scripting
        perl
        python-3
        ;; Git
        git
        ;; Tests
        lief)
  (let ((target (getenv "HOST")))
    (cond ((string-suffix? "-mingw32" target)
           ;; Windows
           (list zip
                 (make-mingw-pthreads-cross-toolchain "x86_64-w64-mingw32")
                 (make-nsis-for-gcc-10 nsis-x86_64)
                 osslsigncode))
          ((string-contains target "-linux-")
           (list (cond ((string-contains target "riscv64-")
                        (make-bitcoin-cross-toolchain target
                                                      #:base-libc (make-glibc-without-werror glibc-2.27/bitcoin-patched)
                                                      #:base-kernel-headers base-linux-kernel-headers))
                       (else
                        (make-bitcoin-cross-toolchain target)))))
          ((string-contains target "darwin")
           (list clang-toolchain-10 binutils cmake xorriso python-signapple))
          (else '())))))

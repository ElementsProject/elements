#!/usr/bin/env bash
#
# Copyright (c) 2018-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

if [[ $QEMU_USER_CMD == qemu-s390* ]]; then
  export LC_ALL=C
fi

# Create folders that are mounted into the docker
mkdir -p "${CCACHE_DIR}"
mkdir -p "${PREVIOUS_RELEASES_DIR}"

export ASAN_OPTIONS="detect_stack_use_after_return=1:check_initialization_order=1:strict_init_order=1"
export LSAN_OPTIONS="suppressions=${BASE_ROOT_DIR}/test/sanitizer_suppressions/lsan"
export TSAN_OPTIONS="suppressions=${BASE_ROOT_DIR}/test/sanitizer_suppressions/tsan:halt_on_error=1:log_path=${BASE_SCRATCH_DIR}/sanitizer-output/tsan"
export UBSAN_OPTIONS="suppressions=${BASE_ROOT_DIR}/test/sanitizer_suppressions/ubsan:print_stacktrace=1:halt_on_error=1:report_error_type=1"
env | grep -E '^(BITCOIN_CONFIG|BASE_|QEMU_|CCACHE_|LC_ALL|BOOST_TEST_RANDOM|DEBIAN_FRONTEND|CONFIG_SHELL|(ASAN|LSAN|TSAN|UBSAN)_OPTIONS|PREVIOUS_RELEASES_DIR)' | tee /tmp/env
if [[ $BITCOIN_CONFIG = *--with-sanitizers=*address* ]]; then # If ran with (ASan + LSan), Docker needs access to ptrace (https://github.com/google/sanitizers/issues/764)
  DOCKER_ADMIN="--cap-add SYS_PTRACE"
fi

export P_CI_DIR="$PWD"

if [ -z "$DANGER_RUN_CI_ON_HOST" ]; then
  echo "Creating $DOCKER_NAME_TAG container to run in"
  LOCAL_UID=$(id -u)
  LOCAL_GID=$(id -g)

  # the name isn't important, so long as we use the same UID
  LOCAL_USER=nonroot
  ${CI_RETRY_EXE} docker pull "$DOCKER_NAME_TAG"

  if [ -n "${RESTART_CI_DOCKER_BEFORE_RUN}" ] ; then
    echo "Restart docker before run to stop and clear all containers started with --rm"
    systemctl restart docker
  fi

  # shellcheck disable=SC2086
  DOCKER_ID=$(docker run $DOCKER_ADMIN --rm --interactive --detach --tty \
                  --mount type=bind,src=$BASE_ROOT_DIR,dst=/ro_base,readonly \
                  --mount type=bind,src=$CCACHE_DIR,dst=$CCACHE_DIR \
                  --mount type=bind,src=$DEPENDS_DIR,dst=$DEPENDS_DIR \
                  --mount type=bind,src=$PREVIOUS_RELEASES_DIR,dst=$PREVIOUS_RELEASES_DIR \
                  -w $BASE_ROOT_DIR \
                  --env-file /tmp/env \
                  --name $CONTAINER_NAME \
                  $DOCKER_NAME_TAG)

  # Create a non-root user inside the container which matches the local user.
  #
  # This prevents the root user in the container modifying the local file system permissions
  # on the mounted directories
  docker exec "$DOCKER_ID" useradd -u "$LOCAL_UID" -o -m "$LOCAL_USER"
  docker exec "$DOCKER_ID" groupmod -o -g "$LOCAL_GID" "$LOCAL_USER"
  docker exec "$DOCKER_ID" chown -R "$LOCAL_USER":"$LOCAL_USER" "${BASE_ROOT_DIR}"
  export DOCKER_CI_CMD_PREFIX_ROOT="docker exec -u 0 $DOCKER_ID"
  export DOCKER_CI_CMD_PREFIX="docker exec -u $LOCAL_UID $DOCKER_ID"
else
  echo "Running on host system without docker wrapper"
fi

CI_EXEC () {
  $DOCKER_CI_CMD_PREFIX bash -c "export PATH=$BASE_SCRATCH_DIR/bins/:\$PATH && cd \"$P_CI_DIR\" && $*"
}
CI_EXEC_ROOT () {
  $DOCKER_CI_CMD_PREFIX_ROOT bash -c "export PATH=$BASE_SCRATCH_DIR/bins/:\$PATH && cd \"$P_CI_DIR\" && $*"
}
export -f CI_EXEC
export -f CI_EXEC_ROOT

if [ -n "$DPKG_ADD_ARCH" ]; then
  CI_EXEC_ROOT dpkg --add-architecture "$DPKG_ADD_ARCH"
fi

if [[ $DOCKER_NAME_TAG == *centos* ]] || [[ $DOCKER_NAME_TAG == *rocky* ]]; then
  ${CI_RETRY_EXE} CI_EXEC_ROOT dnf -y install epel-release
  ${CI_RETRY_EXE} CI_EXEC_ROOT dnf -y --allowerasing install "$DOCKER_PACKAGES" "$PACKAGES"
elif [ "$CI_USE_APT_INSTALL" != "no" ]; then
  if [[ "${ADD_UNTRUSTED_BPFCC_PPA}" == "true" ]]; then
    # Ubuntu 22.04 LTS and Debian 11 both have an outdated bpfcc-tools packages.
    # The iovisor PPA is outdated as well. The next Ubuntu and Debian releases will contain updated
    # packages. Meanwhile, use an untrusted PPA to install an up-to-date version of the bpfcc-tools
    # package.
    # TODO: drop this once we can use newer images in GCE
    CI_EXEC_ROOT add-apt-repository ppa:hadret/bpfcc
  fi
  ${CI_RETRY_EXE} CI_EXEC_ROOT apt-get update
  ${CI_RETRY_EXE} CI_EXEC_ROOT apt-get install --no-install-recommends --no-upgrade -y "$PACKAGES" "$DOCKER_PACKAGES"
fi

if [ -n "$PIP_PACKAGES" ]; then
  if [ "$CI_OS_NAME" == "macos" ]; then
    sudo -H pip3 install --upgrade --break-system-packages pip
    # shellcheck disable=SC2086
    IN_GETOPT_BIN="$(brew --prefix gnu-getopt)/bin/getopt" ${CI_RETRY_EXE} pip3 install --user $PIP_PACKAGES
  else
    # shellcheck disable=SC2086
    ${CI_RETRY_EXE} CI_EXEC pip3 install --user $PIP_PACKAGES
  fi
fi

if [ "$CI_OS_NAME" == "macos" ]; then
  top -l 1 -s 0 | awk ' /PhysMem/ {print}'
  echo "Number of CPUs: $(sysctl -n hw.logicalcpu)"
else
  CI_EXEC free -m -h
  CI_EXEC echo "Number of CPUs \(nproc\):" \$\(nproc\)
  CI_EXEC echo "$(lscpu | grep Endian)"
fi
CI_EXEC echo "Free disk space:"
CI_EXEC df -h

if [ "$RUN_FUZZ_TESTS" = "true" ]; then
  export DIR_FUZZ_IN=${DIR_QA_ASSETS}/fuzz_seed_corpus/
  if [ ! -d "$DIR_FUZZ_IN" ]; then
    CI_EXEC git clone --depth=1 https://github.com/ElementsProject/qa-assets "${DIR_QA_ASSETS}"
  fi
elif [ "$RUN_UNIT_TESTS" = "true" ] || [ "$RUN_UNIT_TESTS_SEQUENTIAL" = "true" ]; then
  export DIR_UNIT_TEST_DATA=${DIR_QA_ASSETS}/unit_test_data/
  if [ ! -d "$DIR_UNIT_TEST_DATA" ]; then
    CI_EXEC mkdir -p "$DIR_UNIT_TEST_DATA"
    CI_EXEC curl --location --fail https://github.com/ElementsProject/qa-assets/raw/master/unit_test_data/script_assets_test.json -o "${DIR_UNIT_TEST_DATA}/script_assets_test.json"
  fi
fi

CI_EXEC mkdir -p "${BASE_SCRATCH_DIR}/sanitizer-output/"

if [[ ${USE_MEMORY_SANITIZER} == "true" ]]; then
  CI_EXEC_ROOT "update-alternatives --install /usr/bin/clang++ clang++ \$(which clang++-12) 100"
  CI_EXEC_ROOT "update-alternatives --install /usr/bin/clang clang \$(which clang-12) 100"
  CI_EXEC "mkdir -p ${BASE_SCRATCH_DIR}/msan/build/"
  CI_EXEC "git clone --depth=1 https://github.com/llvm/llvm-project -b llvmorg-12.0.0 ${BASE_SCRATCH_DIR}/msan/llvm-project"
  CI_EXEC "cd ${BASE_SCRATCH_DIR}/msan/build/ && cmake -DLLVM_ENABLE_PROJECTS='libcxx;libcxxabi' -DCMAKE_BUILD_TYPE=Release -DLLVM_USE_SANITIZER=MemoryWithOrigins -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DLLVM_TARGETS_TO_BUILD=X86 ../llvm-project/llvm/"
  CI_EXEC "cd ${BASE_SCRATCH_DIR}/msan/build/ && make $MAKEJOBS cxx"
fi

if [[ "${RUN_TIDY}" == "true" ]]; then
  export DIR_IWYU="${BASE_SCRATCH_DIR}/iwyu"
  if [ ! -d "${DIR_IWYU}" ]; then
    CI_EXEC "mkdir -p ${DIR_IWYU}/build/"
    CI_EXEC "git clone --depth=1 https://github.com/include-what-you-use/include-what-you-use -b clang_14 ${DIR_IWYU}/include-what-you-use"
    CI_EXEC "cd ${DIR_IWYU}/build && cmake -G 'Unix Makefiles' -DCMAKE_PREFIX_PATH=/usr/lib/llvm-14 ../include-what-you-use"
    CI_EXEC_ROOT "cd ${DIR_IWYU}/build && make install $MAKEJOBS"
  fi
fi

if [ -z "$DANGER_RUN_CI_ON_HOST" ]; then
  echo "Create $BASE_ROOT_DIR"
  CI_EXEC rsync -a /ro_base/ "$BASE_ROOT_DIR"
fi

if [ "$USE_BUSY_BOX" = "true" ]; then
  echo "Setup to use BusyBox utils"
  CI_EXEC mkdir -p "${BASE_SCRATCH_DIR}/bins/"
  # tar excluded for now because it requires passing in the exact archive type in ./depends (fixed in later BusyBox version)
  # find excluded for now because it does not recognize the -delete option in ./depends (fixed in later BusyBox version)
  # ar excluded for now because it does not recognize the -q option in ./depends (unknown if fixed)
  # shellcheck disable=SC1010
  CI_EXEC for util in \$\(busybox --list \| grep -v "^ar$" \| grep -v "^tar$" \| grep -v "^find$"\)\; do ln -s \$\(command -v busybox\) "${BASE_SCRATCH_DIR}/bins/\$util"\; done
  # Print BusyBox version
  CI_EXEC patch --help
fi

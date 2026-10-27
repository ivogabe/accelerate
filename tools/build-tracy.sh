#!/usr/bin/env bash

# This script builds Tracy executables to collect and view profiling data from
# supported backends.  Executable tracy-profiler provides a GUI, while
# executable tracy-capture provides a CLI.
#
# The Tracy repository in the Git submodule is used.  The version must exactly
# match the version used when building Accelerate with Tracy enabled.  After
# cloning the repository, initialize submodules via:
#
#     git submodule update --init --recursive
#
# External dependencies:
#
# * cmake
# * pkg-config
# * freetype2
# * glfw3
# * gtk3 (Linux only)
# * TBB (should be part of your compiler toolchain)
#
# For example on Debian/Ubuntu you can install all of these via:
#
#     sudo apt install cmake pkg-config libfreetype-dev libglfw3-dev libgtk-3-dev libtbb-dev
#
# Or on macOS via:
#
#     brew install cmake pkg-config freetype glfw


# TODO Configure cmake options based on system and/or CLI options


set -o errexit
set -o nounset
set -o pipefail
#set -o xtrace


##############################################################################
# Globals

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
PROJECT_DIR="$(realpath "${SCRIPT_DIR}/..")"
SUBMODULE='cbits/tracy'
REPO_DIR="${PROJECT_DIR}/${SUBMODULE}"
BUILD_DIR="${PROJECT_DIR}/build-tracy"

# LEGACY=1 builds with X11 instead of Wayland
CMAKE_GENERATE_OPTS=( -D'CMAKE_BUILD_TYPE=Release' -D'LEGACY=1' )

CMAKE_BUILD_OPTS=( --config 'Release' -j 2 )


##############################################################################
# Functions

usage() {
  echo "Usage: $0"
  echo
  echo 'Build Tracy executables'
  echo
  echo 'Exit codes:'
  echo '  0  success'
  echo '  1  failure'
  echo '  2  usage error'
}

info() {
  echo "[INFO] $*"
}

notice() {
  echo "[NOTICE] $*"
}

die() {
  echo "[ERROR] $*" >&2
  exit 1
}

check_repo() {
  local status
  if [ ! -d "${REPO_DIR}" ] ; then
    die "Tracy repository not found: ${REPO_DIR}"
  fi
  if ! status="$(git submodule status -- "${REPO_DIR}" 2>&1)" ; then
    die "cannot get status of ${SUBMODULE} submodule: ${REPO_DIR}"
  fi
  if [[ -z "${status}" ]] ; then
    die "${SUBMODULE} is not a submodule: ${REPO_DIR}"
  fi
  info "status: ${status}"
  case "${status:0:1}" in
    '-' )
      die 'submodule is not initialized'
      ;;
    '+' )
      notice 'submodule is at a different revision'
      ;;
    'U' )
      notice 'submodule has merge conflicts'
      ;;
    ' ' )
      ;;
  esac
}

check_build_dir() {
  test ! -e "${BUILD_DIR}" || die "Tracy build directory exists: ${BUILD_DIR}"
}

build() {
  local component="$1"
  local target_dir="${BUILD_DIR}/tmp/${component}"
  info "building ${component}"
  mkdir -p "${target_dir}"
  cmake \
    -B "${target_dir}" \
    -S "${REPO_DIR}/${component}" \
    -D"CMAKE_INSTALL_PREFIX=${BUILD_DIR}" \
    "${CMAKE_GENERATE_OPTS[@]}"
  cmake \
    --build "${target_dir}" \
    "${CMAKE_BUILD_OPTS[@]}"
  cmake --install "${target_dir}"
  rm -rf "${BUILD_DIR}/tmp"
}


##############################################################################
# Main

for arg in "$@" ; do
  case "${arg}" in
    '-h' | '--help' )
      usage
      exit 0
      ;;
    -* )
      echo "error: unknown option: ${arg}" >&2
      echo >&2
      usage >&2
      exit 2
      ;;
    * )
      echo "error: unknown argument: ${arg}" >&2
      echo >&2
      usage >&2
      exit 2
      ;;
  esac
done

check_repo
check_build_dir
build 'capture'
build 'profiler'

FROM centos:centos7.6.1810

RUN set -x \
    && yum install -y epel-release \
    && yum install -y \
    rpm-build \
    git \
    && git clone https://github.com/commerceblock/ocean.git -b docker_rpm_spec \
    && cd ocean/contrib/docker/rpm-build \
    && rpmbuild ocean.spec

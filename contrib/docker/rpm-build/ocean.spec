Name:           ocean
Version:        1.0
Release:        1
Summary:        oceand ocean-cli and ocean-tx binaries
License:        MIT
URL:            https://github.com/commerceblock/ocean
Source0:        https://github.com/commerceblock/ocean/archive/master.zip
Packager:       Martin Tsvetanov
Requires:       glibc
BuildRoot:      ~/rpmbuild/

%description
oceand ocean-cli and ocean-tx binaries

%prep
echo "BUILDROOT = $RPM_BUILD_ROOT"
mkdir -p $RPM_BUILD_ROOT/usr/local/bin/
cp ~/ocean/src/oceand $RPM_BUILD_ROOT/usr/local/bin/oceand
cp ~/ocean/src/ocean-cli $RPM_BUILD_ROOT/usr/local/bin/ocean-cli
cp ~/ocean/src/ocean-tx $RPM_BUILD_ROOT/usr/local/bin/ocean-tx
exit

%clean
rm -rf %{buildroot}
rm -rf $RPM_BUILD_ROOT/usr/local/bin

%files
%{_bindir}/oceand
%{_bindir}/ocean-cli
%{_bindir}/ocean-tx

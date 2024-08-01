## PGP keys of builders and Developers

The file `keys.txt` contains fingerprints of the public keys of builders and
active developers.

The associated keys are mainly used to sign git commits or the build results
of Guix builds.

The most recent version of each pgp key can be found on most pgp key servers.

Fetch the latest version from the key server to see if any key was revoked in
the meantime.
To fetch the latest version of all pgp keys in your gpg homedir,

```sh
gpg --refresh-keys
```

To fetch keys of builders and active developers, feed the list of fingerprints
of the primary keys into gpg:

On \*NIX:
```sh
while read fingerprint keyholder_name; do gpg --keyserver hkps://keys.openpgp.org --recv-keys ${fingerprint}; done < ./keys.txt
```

On Windows (requires Gpg4win >= 4.0.0):
```
FOR /F "tokens=1" %i IN (keys.txt) DO gpg --keyserver hkps://keys.openpgp.org --recv-keys %i
```

Add your key to the list if you provided Guix attestations for two major or
minor releases of Bitcoin Core.

Requirements
===

Tested on:

- `ghc` of version 7.10.2
- `cabal` of version 1.22
- `gcc` of version 4.6.3

Ubuntu 12.04.5 LTS
===

Install GCC:

```bash
sudo apt-get update
sudo apt-get install gcc
```

Install Haskell and Cabal through a 3rd party PPA:

```bash
sudo apt-get update
sudo apt-get install -y software-properties-common python-software-properties
sudo add-apt-repository -y ppa:hvr/ghc
sudo apt-get update
sudo apt-get install -y cabal-install-1.22 ghc-7.10.2 ghc-7.10.2-prof
cat >> ~/.bashrc <<EOF
export PATH="\$HOME/.cabal/bin:/opt/cabal/1.22/bin:/opt/ghc/7.10.2/bin:\$PATH"
EOF
export PATH=~/.cabal/bin:/opt/cabal/1.22/bin:/opt/ghc/7.10.2/bin:$PATH
```

Update Cabal's sources:

```bash
cabal update
```

Upgrade the versions of `alex` and `happy` because they are likely to be
outdated in the default distribution.

```bash
cabal install alex
cabal install happy
```

Build the project:

```bash
bash ./build.sh
```


Mac OS X
===

Install GHC version 7.10.2 from https://ghcformacosx.github.io/ and you are done.

Linux virtualization on Mac OS X
===

Using [Vagrant](https://www.vagrantup.com/) run Ubuntu 12.04.5 LTS and then
follow the instructions from above. To prepare and run Vagrant run:

```bash
vagrant up
vagrant ssh
```

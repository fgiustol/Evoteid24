This is a prototype implementation of a voting system based on the paper "Efficient Cleansing in Coercion-Resistant Voting" by Rosario Giustolisi and Maryam Sheikhi accepted to EVOTEID 2024.

It requires [zksk](https://github.com/spring-epfl/zksk) for the implementation of disjunctive zero-knowledge proofs. Make sure that it is installed correctly by following the [zksk instructions](https://github.com/spring-epfl/zksk#getting-started).

It also requires the attrs python packages, which can be obtained by pip
```
pip install attrs
```

## MacOS

It has been tested on MacOS Sonoma 14.5 with Homebrew Python3. Known issues with the installation of zksk and its dependencies could be addressed by installing openssl version 1.1
```
brew install openssl@1.1
```


and setting path and environment variables according to the output of ``` brew info openssl@1.1 ```. For example:
```
export LDFLAGS="-L/opt/homebrew/opt/openssl@1.1/lib"
export CPPFLAGS="-I/opt/homebrew/opt/openssl@1.1/include"
export PKG_CONFIG_PATH="/opt/homebrew/opt/openssl@1.1/lib/pkgconfig"

```


## Contacts
Rosario Giustolisi <rosg@itu.dk>

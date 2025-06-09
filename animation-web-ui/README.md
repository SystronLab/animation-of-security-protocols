This repository contains an animation Web UI implemented with [Yesod](https://www.yesodweb.com/). This repository is created using a template of Yesod. Refer to the [Yesod Quickstart guide](https://www.yesodweb.com/page/quickstart) for additional detail.

## Haskell Setup

1. If you haven't already, [install Stack](https://haskell-lang.org/get-started)
	* On POSIX systems, this is usually `curl -sSL https://get.haskellstack.org/ | sh`
2. Install the `yesod` command line tool: `stack install yesod-bin --install-ghc`
3. Build libraries: `stack build`

If you have trouble, refer to the [Yesod Quickstart guide](https://www.yesodweb.com/page/quickstart) for additional detail.

## PlantUML Server
Install the PlantUML server from [here](https://github.com/plantuml/plantuml-server) and then run `mvn jetty:run`. Now the server is running locally, you can open [http://localhost:8080/plantuml/](http://localhost:8080/plantuml/) to check its status.

## Development

Start a development server with:

```
stack exec -- yesod devel
```

As your code changes, your site will be automatically recompiled and redeployed to localhost.

## Tests

```
stack test --flag animation-web-ui:library-only --flag animation-web-ui:dev
```

(Because `yesod devel` passes the `library-only` and `dev` flags, matching those flags means you don't need to recompile between tests and development, and it disables optimization to speed up your test compile times).

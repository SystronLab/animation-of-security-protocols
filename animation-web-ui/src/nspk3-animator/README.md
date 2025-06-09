This project is intended to be a simple animation library for the Needham-Schroeder Public Key Protocol (3-message version) for use with
the animation web interface. 

# nspk3-animator
Most of code is automatically generated from the Isabelle/HOL. Then it is compiled into a Haskell library using 
- `stack new nspk3-animator new-template`
- `stack build`
- `stack exec nspk3-animator-exe`

# animation-web-ui
- build: `stack build`
- run: `stack exec -- yesod devel` 

## Investigations 
### Manual animation
- How to store explored states?
  + Sessions: good for the storage of small data, based on pairs of keys and values (of type **string**) 
    * Server-side sessions: `serversession`
      + DB: `persistent`
      + Acid: in memory 
  + Persistent DB
      + Table is set in `Models.hs`
      + But how to store Itree in DB?
        * In general, you need to serialize a data type to a string, and reconstruct it from the string when extracting from DB. 
        * So these data types should be with `show` and `read` functions
        * Our Itree has no such functions, and also generic. 
  + Or we can explore the ITree in the beginning of the we applicaiton, and store it in the DB. Then all future functions will be based on the ITree stored in DB. 

# Build and installation issues
- Could not load module ‘Text.Show.Pretty’
    * `$ stack install pretty-show`

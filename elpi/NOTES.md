# Random notes

## How to load

1. Start the docker container:
   ```
   ./Docker/docker-holelpi.sh 
   ```
2. Start OCaml:
   From the toplevel directory:
   ```
   rlwrap ocaml -I `camlp5 -where` `camlp5 -where`/gramlib.cma
   ```
3. Load hol:
   ```
   #use "make.ml";;
   ```
4. Load the Elpi extension:
   ```
   loadt "elpi/make.ml";;
   ```

## Manually test one entry

1. Load the trace code:
   ```
   loadt "elpi/trace_parsed_terms.ml";;
   ```
2. Load the saved trace:
   ```
   let pterms = load_parsed_terms "elpi/CORE.bin";;
   ```
3. Pick a term:
   ```
   let stm,ptm,ift = el 2 pterms;;
   ```
4. Run the elaborator on the string:
   ```
   let qtm = Hol_elpi.quotation stm;;
   ```

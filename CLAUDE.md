# prg_lean_01

Progetto Lean 4 gestito con Lake. Rispondimi in italiano; nel codice usa identificatori
e commenti in inglese.

## Struttura
- `lakefile.toml`: configurazione di Lake (pacchetto `prg_lean_01`, libreria `PrgLean01`).
- `PrgLean01.lean`: file radice della libreria, importa tutti i moduli della libreria.
- `PrgLean01/`: moduli della libreria, uno per file (`PrgLean01/Basic.lean` si importa con `import PrgLean01.Basic`).
- `lean-toolchain`: versione di Lean usata dal progetto (la gestisce elan).
- `lake-manifest.json`: versioni bloccate delle dipendenze.
- `.lake/`: compilati e dipendenze scaricate. Puoi leggerlo, non modificarlo mai.

## Comandi
- Compila tutto: `lake build`
- Controlla un solo file (compila prima i suoi import): `lake lean PrgLean01/Basic.lean`
- Se `lake build` si mette a ricompilare Mathlib, riscarica la cache: `lake exe cache get`

## Regole
- Il progetto usa Lean 4 alla versione indicata in `lean-toolchain`: niente sintassi di Lean 3 (`begin ... end`).
- Dopo ogni modifica a un file `.lean`, controllalo con `lake lean <file>` o `lake build` e correggi
  tutti gli errori prima di dire che hai finito.
- Un teorema è dimostrato solo se il file compila senza errori e senza `sorry`. Se resta un `sorry`,
  dimmelo e spiega cosa manca.
- Non aggiungere `axiom`, non usare `sorry` per far passare la build e non cambiare l'enunciato di un
  teorema senza chiedermelo. Se un enunciato sembra falso, fermati e spiegami perché.
- Non inventare nomi di lemmi: verifica con `#check` che esistano prima di usarli.
- Ogni nuovo file della libreria va importato in `PrgLean01.lean`, altrimenti `lake build` non lo compila.
- Non modificare `lean-toolchain`, `lake-manifest.json` o le dipendenze in `lakefile.toml` e non eseguire
  `lake update` senza chiedermelo: cambiano le versioni di Lean e delle librerie per tutto il progetto.
- Nomi: teoremi e lemmi in `snake_case`, tipi e strutture in `UpperCamelCase`, funzioni e definizioni
  in `lowerCamelCase`. Righe di massimo 100 caratteri.

## Dimostrazioni
1. Scrivi prima l'enunciato e lo scheletro, con i passaggi intermedi come `have h : ... := by sorry`,
   e verifica che compili.
2. Chiudi un `sorry` alla volta, ricompilando dopo ognuno.
3. Alla fine verifica con `#print axioms nome_teorema` che il risultato non dipenda da `sorryAx`,
   poi togli il comando.
- Prima di scrivere un lemma ausiliario cerca se esiste già: `exact?`, `apply?`, `simp?`, `#check`.
- Per trovare i nomi dei lemmi puoi cercare con `rg` in `.lake/packages/mathlib/Mathlib/`.

## Strumenti
- Se è configurato il server MCP `lean-lsp`, usalo per leggere lo stato degli obiettivi e i messaggi
  di errore di un file e per cercare lemmi, invece di ricompilare tutto a ogni passo.

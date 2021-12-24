# Eksperiment

## E1

```
make SKIP=17000 LIMIT=2
```

Traja na Macu 10 min, cca 3 GB na grafu s 102 vozlišči in cca 7 GB na grafu z 134 vozlišči.

## E2

Pri Juretu zmanjka spomina na

```
make SKIP=18000 LIMIT=2
```

Opozorila za ekscesno porabo spomina javlja `lean --profile --memory=1000` že pri 

```
make convert SKIP=15000 LIMIT=2
```

## E3
Za `make convert LIMIT=2 SKIP=18000` mi pri lean ukazu 
```
lean --profile --memory=20000 --make src/hog/data
```
Zmanjka spomina pri preverjanju števila vozlišč. Dobim error
```
error: excessive memory consumption detected at 'replace' (potential solution: increase memory consumption threshold)
```
Buildanje .olean datoteke se potem ustavi.

## E4

```
make SKIP=16000 LIMIT=2
```

Porabi nekje med 2 in 2.5 GB, `olean` datoteki sta cca 1000x manjši.
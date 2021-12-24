# Eksperiment

# E1

```
make SKIP=17000 LIMIT=2
```

Traja na Macu 10 min, cca 3 GB na grafu s 102 vozlišči in cca 7 GB na grafu z 134 vozlišči.

# E2

Pri Juretu zmanjka spomina na

```
make SKIP=18000 LIMIT=2
```

Opozorila za ekscesno porabo spomina javlja `lean --profile --memory=1000` že pri 

```
make convert SKIP=15000 LIMIT=2
```
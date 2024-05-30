# Osservazioni fatte in tutto il progetto

Magari poi lo chiamiamo _README.md_

## CP

1. Dividere equamente il carico toglie una quantità spropositata di soluzioni non ottimali.
2. Un'istanza può essere sbagliata?
3. È giusto assumere la distanza euclidea?

## SAT

* [X] Semplificare a -> b con -a  \\/ b (NON CAMBIA NIENTE però a davidino cambiava uffa) (**riprovare se ottimi un modello migliore nel frattempo**)
* [X] Provare a cambiare il range delle distanze nelle istanze simmetriche `for i2 in range(i1+1, num_items)` (NON CAMBIA NIENTE) (**riprovare se ottimi un modello migliore nel frattempo**)
* [X] Pulire i constraint anche nel 1-hot model
* [ ] Collegare bene il launcher con il main (`solve_instance` richiede modello e strategia di ricerca ora), ultimo dei problemi prima trovare una soluzione presentabile
* [ ] Rompere il subcircuit

## SMT

bisogna capire come strutturare la ricerca. z3 ha un minimize/maximize, altri solver no. non so se farglielo usare o ocntinuare a partire dal lower bound e vedere se è sat

## MIP

## GENERICHE:

- BISOGNA CONTARE IL TEMPO DI COMPUTAZIONE DI LOWER E UPPER BOUND
- Bisogna rendere interattiva l'interfaccia docker
- bisogna tener conto che se ci sono preoperazioni sui file tc andrebbe tolto il tempo max di risoluzione al solve. per dire che se ci metto 1 secondo a fare certe operaizoni sulle isnatnze, al solver dovrei dare solo 299 secondi
- mi sa tanto che prima o poi tocca aggiustare il discorso dei percorsi.... ehehehheehhe
- LE SIMEMTRIE FANNO MERDA

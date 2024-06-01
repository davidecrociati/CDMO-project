# Osservazioni fatte in tutto il progetto

Magari poi lo chiamiamo _README.md_

## CP

1. Dividere equamente il carico toglie una quantità spropositata di soluzioni non ottimali.
2. Un'istanza può essere sbagliata?
3. È giusto assumere la distanza euclidea?

## SAT

* [X] Semplificare a -> b con -a  \\/ b
* [X] Provare a cambiare il range delle distanze nelle istanze simmetriche `for i2 in range(i1+1, num_items)`
* [X] Collegare bene il launcher con il main (`solve_instance` richiede modello e strategia di ricerca ora), ultimo dei problemi prima trovare una soluzione presentabile
* [X] Provare simmetrie nel modello e approcci diversi
* [X] Rivedere meglio il modello per pulire/migliorare
* [ ] @davidino prova a lanciare le istanze per vedere se cambia qualcosa
* [X] Rendere selezionabile la simmetria dal launcher per i test

Da notare che:

1. Per la **inst16** la migliore è la binary-search con la binary_cut=15 altrimenti le altre o sono troppo vicine all'ottimale e non danno risultati oppure sono troppo lontane e ci mettono troppo a scendere
2. La **inst19** non riesce a trovare una soluzione nemmeno col upper_bound :(
3. Le altre istanze hanno problemi a caricare i constraint e questo è un problema meccanico di avere troppi dati e troppe iterazioni per farci tutti i constraint, alcuni come la 11 ci mettono anche più di 20 min di cui 5 o 6 anche solo senza distanze (se non ricordo male) quindi c'è poco da fare con le simmetrie.
4. Con le simmetria riesco a risolvere la 16 ma non torna la distanza massima (COME CAZZO È POSSIBILE MADONNA SANTA)

## SMT

bisogna capire come strutturare la ricerca. z3 ha un minimize/maximize, altri solver no. non so se farglielo usare o ocntinuare a partire dal lower bound e vedere se è sat

## MIP

## GENERICHE:

- BISOGNA CONTARE IL TEMPO DI COMPUTAZIONE DI LOWER E UPPER BOUND
- Bisogna rendere interattiva l'interfaccia docker
- bisogna tener conto che se ci sono preoperazioni sui file tc andrebbe tolto il tempo max di risoluzione al solve. per dire che se ci metto 1 secondo a fare certe operaizoni sulle isnatnze, al solver dovrei dare solo 299 secondi
- mi sa tanto che prima o poi tocca aggiustare il discorso dei percorsi.... ehehehheehhe
- LE SIMEMTRIE FANNO MERDA

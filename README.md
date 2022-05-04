# MLinterpreter

L'interprete sem creato valuta espressioni di tipo exp. L'ambiente che utilizza ha un tipo polimorfo ed utilizza le liste come struttura di base, simile a quello visto a lezione. Nell'interprete viene fatto un match delle possibili espressioni e vengono valutate nell'ambiente passato.  Si è scelto di non creare una vera e propria funzione di typechecking, ma di utilizzare il sistema match, l'impossibilità di un argomento di essere matchato implica un errore di tipo. Le scelte più particolare sono legate alle tuple. Queste  vengono valutate applicando su ogni elemento l'interprete, ciò avviene usando la funzione map implementata in List. Le altre funzioni legate alle tuple, un po' più particolari, sono la At, la Slice ed il For. La prima valuta gli argomenti passati, se il match avviene correttamente, invoca una funzione ausiliaria, che dati un intero k e una lista l restituisce l'elemento k-esimo di l se esso è positivo, nel caso k fosse negativo restituisce l'elemento k considerando l'ultima posizione di l come -1, andando a diminuire sempre più si avvicina alla testa della lista. L'altra funzione agisce similmente applicando la precedente funzione ausiliaria a tutti gli elementi compresi nelle posizioni degli interi passati, con il primo parametro minore del secondo. Il For, dopo aver controllato che gli sia stata passata una tupla, chiama una funzione che al suo interno applica su  ogni elemento della tupla l'espressione passata come parametro valutata  con un nuovo bind tra l'elemento e l'identificatore passato, se quest'ultima funzione non da errore se ne inserisce il risultato nella tupla valutata, altrimenti lo si scarta.
Per testare l'interprete si usa una lista, formata da coppie test e risultato atteso, che viene passata ad una funzione nella quale si stampa a video il risultato della valutazione dell'interprete e un booleano, true se la valutazione coincide con l'atteso, false altrimenti.
	
	
	
a cura di Dan Dorin Izvoreanu

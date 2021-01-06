# Dijkstra_Coq
An implementation of Dijkstra Algorithm in Coq. (just for practice)

## Data Structure 

![image](https://drive.google.com/uc?export=view&id=1AmNZZlnc10aALEuqby2AGYPVg6EfGre8)

## How are Graphs represented? 

A graph has the following type : list(node * (list (node * nat))))

i.e.

It is nothing but a list of pairs, of the following form:

(Node 1, [ (Node 2,1); (Node 3,2)] )

This represents the structure of a graph where:
There are 3 nodes = Node 1, Node 2 and Node 3
* Node 1 is connected to:
    * Node 2 at a distance of 1 unit
    * Node 3 at a distance of 2 units

## Example: 
![image](https://drive.google.com/uc?export=view&id=1nKaiO6lhEehrqZHM5BUay1b0maIw4fPH)

![image](https://drive.google.com/uc?export=view&id=1wcJ65gLrwUEwBtkpGYkCUWk7l4C94DS2)

## Output:

On runnning the function: <br/>
![image](https://drive.google.com/uc?export=view&id=1uRW1iWaWVrTSHZG5ar_ekBDpMRK5i0a_)



We get: <br/>
![image](https://drive.google.com/uc?export=view&id=1_QqunrGPlXhfI4eTtUnaEGXSMar-MYEf)


## Assumptions: 

First and foremost, this is just a mock implementation I wrote just to get a better understanding of the COQ proof assistant. If I had to rewrite this, I would change A LOT of things. 

* The largest possible distance between two nodes is taken to be 1000. 
* If a node is not reachable, then it is simply marked (Node 1000, 1000) in the output. 


(*
  Course: CMSC631 - Program Analysis and Understanding
  Topic: Implementation of Dijsktra algorithm in COQ 
  Author: Ujjwal Ayyangar
  Semester: Fall 2020
  Instructor: Leonidas Lampropoulos
*)

Require Import Coq.omega.Omega.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

(* Definition the structure of a GRAPH *)

(* NODE *)
Inductive node :=
  | Node : nat -> node.

(* Equality of nodes *) 


Definition is_equal(node_a node_b : node): bool :=
  match node_a, node_b with
    | Node a, Node b => beq_nat a b
end.

(* Some examples for testing equality of Nodes *) 

Example test_eq1: (is_equal (Node 1) (Node 1)) = true.
Proof.
  reflexivity. 
Qed.

Example test_eq2: (is_equal (Node 1) (fst (Node 1, [Node 2; Node 4]) ) ) = true.
Proof.
  reflexivity. 
Qed.

Example test_eq3: (is_equal (Node 1) (Node 2)) = false.
Proof.
  reflexivity. 
Qed.


(* How are Graphs represented? 

A graph has the following type : list(node * (list (node * nat)))) 

i.e. 

It is nothing but a list of pairs, of the following form: 

(Node 1, [ (Node 2,1); (Node 3,2)] )

This represents the structure of a graph where:
* There are 3 nodes = Node 1, Node 2 and Node 3
* Node 1 is connected 
  - Node 2 at a distance of 1 unit
  - Node 3 at a distance of 2 units 

*)

(* Below is a sample Graph that I have used for tests below *)

Definition customGraph := 
  [(Node 1, [ (Node 2,1); (Node 3,2)] );
    (Node 2, [ (Node 4,5); (Node 5,2)] );
   (Node 3, [(Node 6,1); (Node 7,2)] );
    (Node 4, [(Node 8,4); (Node 9, 7)])].

Definition custom_node_list :=
  [ (Node 2,1); (Node 3,2); (Node 4,5); (Node 5,2);(Node 6,1); (Node 7,2);(Node 8,4); (Node 9, 7) ].

Definition dup_node_list :=
  [ (Node 2,1); (Node 3,2); (Node 4,5); (Node 5,2); (Node 5,2); (Node 5,2)].


(* Operations on Graph *)


(* Get neighbors of a node in the graph 

Input: A graph and it's node. 
Output: A list of type list(node*nat), containing all the neigbors & their respective distances
        from the neighbouring nodes.

*)

Fixpoint get_neigh
(graph: list(node * (list (node * nat)))) (query_node : node)  : list (node*nat) :=
match graph with
    | h :: t => match (is_equal query_node (fst h)) with
              | true => snd h
              | false => get_neigh t query_node 
              end
    | _ => []
end.


Example test_neigh_1: (get_neigh customGraph (Node 1)) = [(Node 2, 1); (Node 3, 2)].
Proof.
  reflexivity.
Qed.

Example test_neigh_2: (get_neigh customGraph (Node 4)) = [(Node 8, 4); (Node 9, 7)].
Proof.
  reflexivity.
Qed.


(* Most of the structures in my implementation are of the type -list(node*nat), as
you will see later. 

This is nothing but a list which contains pairs of Node and natural number. 

A pair of a Node and a natural number is called node_pair

Therefore, I call list of these pairs, node_pair_list. 

Below are some of the utility functions built to manipulate a node_pair_list

*)


(* Get the smallest node_pair_list 

Function name: get_smallest_npl

Input: A node pair list of type list(node*nat)
Output: Smallest node_pair of type (node*nat)

*)

(* helper function *)
Fixpoint get_smallest_npl_aux (np_list: list (node*nat)) (dist_node: node*nat) :  (node*nat) :=
   match np_list with
    | nil =>  dist_node 
    | h :: t => match (ltb (snd h) (snd dist_node)) with
                | true => get_smallest_npl_aux  t h
                | false => get_smallest_npl_aux t dist_node
                end
    end.


Definition get_smallest_npl (np_list: list (node*nat)) :  (node*nat) :=
   get_smallest_npl_aux np_list ((Node 1000),1000).

Compute( get_smallest_npl []).

Example test_smallest_npl: ( get_smallest_npl custom_node_list) = (Node 2, 1).
Proof.
  reflexivity.
Qed.

(* Remove a node_pair from the node_pair_list 

Function name: remove_node_npl

Input: A node_pair_list and a node.
Output: A node_pair_list with the node removed.

*)

Fixpoint remove_node_npl
(np_list: list (node * nat)) (del_node : node) : list (node*nat) :=
 match np_list with 
  | nil => np_list
  | h :: t => match(is_equal (fst h) del_node) with 
            | true => remove_node_npl t del_node
            | false => h :: (remove_node_npl t del_node)
            end
end.


Example test_remove_node_npl_1: (remove_node_npl custom_node_list (Node 2)) = [(Node 3, 2); (Node 4, 5); (Node 5, 2); (Node 6, 1); (Node 7, 2); (Node 8, 4); (Node 9, 7)].
Proof.
  reflexivity.
Qed.

Example test_remove_node_npl_2: (remove_node_npl custom_node_list (Node 100)) = [(Node 2, 1); (Node 3, 2); (Node 4, 5); 
       (Node 5, 2); (Node 6, 1); (Node 7, 2); 
       (Node 8, 4); (Node 9, 7)].
Proof.
  reflexivity.
Qed.

Example test_remove_node_npl_3: (remove_node_npl [] (Node 100)) = [].
Proof.
  reflexivity.
Qed.



(* Update values in node pairs by a constant value

Function name: update_dist_npl

Input: A node_pair_list and a natural number.
Output: A node_pair_list with values updated.

*)


Fixpoint update_dist_npl
(np_list : list(node*nat)) (dist: nat): list(node*nat) :=
  match np_list, dist with
    | nil, _ => np_list
    | _, O => np_list
    | h :: t, _ =>  ( (fst h), (add (snd h) dist) ) :: update_dist_npl t dist
end.

Compute (update_dist_npl custom_node_list 0).


Example test_update_dist_npl_1: (update_dist_npl custom_node_list 30) = [(Node 2, 31); (Node 3, 32); (Node 4, 35);
       (Node 5, 32); (Node 6, 31); (Node 7, 32);
       (Node 8, 34); (Node 9, 37)].
Proof.
  reflexivity.
Qed.

Example test_update_dist_npl_2: (update_dist_npl custom_node_list 0) = [(Node 2, 1); (Node 3, 2); (Node 4, 5); (Node 5, 2); 
       (Node 6, 1); (Node 7, 2); (Node 8, 4); (Node 9, 7)].
Proof.
  reflexivity.
Qed.

Example test_update_dist_npl_3: (update_dist_npl [] 30) = [].
Proof.
  reflexivity.
Qed.


(* Extract nodes from node_pair_list

Function name: extract_nodes_npl

Input: A node_pair_list 
Output: A list of nodes.

*)

Fixpoint extract_nodes_npl 
(np_list: list (node * nat)) : list(node) :=
  match np_list with
  | [] => []
  | h :: t => (fst h) :: (extract_nodes_npl t)
end.


Example test_extract_nodes_npl_1: (extract_nodes_npl custom_node_list) = [Node 2; Node 3; Node 4; Node 5; 
       Node 6; Node 7; Node 8; Node 9].
Proof.
  reflexivity.
Qed.

Example test_extract_nodes_npl_2: (extract_nodes_npl []) = [].
Proof.
  reflexivity.
Qed.


(* Extract value of a node from node_pair_list
Function name: get_val_npl

Input: A node_pair_list 
Output: A value (nat).

*)

Fixpoint get_val_npl
(np_list: list(node*nat))
(query_node: node) : nat := 
  match np_list with
  | h :: t => match is_equal (fst h) query_node with
              | true => snd h
              | false => get_val_npl t query_node
              end
  | _ => 1000
end.

Compute (get_val_npl custom_node_list (Node 5)).


Example test_get_val_npl_1: (get_val_npl custom_node_list (Node 2))= 1.
Proof.
  reflexivity.
Qed.

Example test_get_val_npl_2: (get_val_npl custom_node_list (Node 5))= 2.
Proof.
  reflexivity.
Qed.

Example test_get_val_npl_3: (get_val_npl [](Node 3))= 1000.
Proof.
  reflexivity.
Qed.



(* Check for a node in a list

Function name: node_in_list

Input: A list of nodes
Output: True or False depending upon the existence of the node.

*)


Fixpoint node_in_list
(nodes: list(node)) (query_node : node) : bool :=
  match nodes with 
   | [] => false
   | h :: t => match (is_equal h query_node) with
              | true => true
              | false => node_in_list t query_node
              end
   end.

Compute (node_in_list [Node 1; Node 3; Node 4] (Node 1)).

Example node_in_list_1: (node_in_list [Node 1; Node 3; Node 4] (Node 1)) = true.
Proof.
  reflexivity.
Qed.

Example node_in_list_2: (node_in_list [Node 1; Node 3; Node 4] (Node 5)) = false.
Proof.
  reflexivity.
Qed.

Example node_in_list_3: (node_in_list [] (Node 1)) = false.
Proof.
  reflexivity.
Qed.


(* Convert a list of nodes to a unique list of nodes.

Function name: unique_list

Input: A list of nodes with possible duplication of nodes.
Output: A unique list of nodes.

*)


Fixpoint unique_list_aux
(old_list: list(node)) (new_list: list(node)) : list(node) :=
  match old_list with 
  | [] => new_list
  | h :: t => match (node_in_list new_list h) with
              | true => unique_list_aux t new_list
              | false => unique_list_aux t (new_list ++ [h])
              end
  end. 

Definition unique_list
(nodes : list(node)) : list(node):=
  unique_list_aux nodes [].

Compute (unique_list (extract_nodes_npl dup_node_list)).

Example unique_list_1: (unique_list (extract_nodes_npl dup_node_list))= [Node 2; Node 3; Node 4; Node 5].
Proof.
  reflexivity.
Qed.

Example unique_list_2: (unique_list [])= [].
Proof.
  reflexivity.
Qed.


(*Remove a node from a list of nodes.

Function name: remove_node

Input: A list of nodes and a node to be removed
Output: List of nodes with the node removed.

*)

Fixpoint remove_node_aux
(nodes: list(node)) (query_node : node) (seen: list(node)) : list(node) :=
match nodes with
  | h :: t => match is_equal h query_node with
            | true => seen ++ t
            | false =>  remove_node_aux t query_node (seen ++ [h])
            end
  | [] => []
  end.

Definition remove_node
(nodes: list(node)) (query_node: node) : list(node) := 
  remove_node_aux nodes query_node [].

Compute (remove_node [] (Node 5)).

Example test_remove_node_1: (remove_node [Node 2; Node 3; Node 4; Node 5] (Node 2)) = [Node 3; Node 4; Node 5].
Proof.
  reflexivity.
Qed.

Example test_remove_node_2: (remove_node [Node 2; Node 3; Node 4; Node 5] (Node 5))= [Node 2; Node 3; Node 4].
Proof.
  reflexivity.
Qed.

Example test_remove_node_3: (remove_node [] (Node 5)) = [].
Proof.
  reflexivity.
Qed.



(*Remove a node from a list of nodes.

Function name: all_nodes

Input: A graph
Output: List of nodes in the graph.

*)

Fixpoint all_nodes_aux
(graph: list(node * (list (node * nat)))) (node_list: list(node)) : (list node) :=
match graph with 
  | [] => node_list
  | h :: t =>  all_nodes_aux t 
               (unique_list ([(fst h)] ++ node_list ++ (extract_nodes_npl (get_neigh graph (fst h)))))
  end.

Definition all_nodes (graph: list(node * (list (node*nat)))) : list(node) :=
  all_nodes_aux graph [].


Example test_all_nodes: (all_nodes customGraph)= [Node 4; Node 3; Node 2; Node 1; 
       Node 5; Node 6; Node 7; Node 8; Node 9].
Proof.
  reflexivity.
Qed.



(* Dijkstra algorithm 

What is it? It is an algorithm for finding the shortest path between two nodes in a graph. 

Input: 

A graph of type list(node * (list (node * nat)))) (as explained above)
A source node of type node, from where the distance of all the nodes will be calculated. 

Output:

The output is given in the form of a distance node_pair_list. 

The distance node_pair_list is a node_pair_list in which the the value in a node_pair, represent the shortest distance
between the node in that node_pair and the source node. 

In the beginning, all the distances are initialized to 1000 

The function below "init_dist" takes in a graph and initializes a distance node_pair_list with all distances at 1000.

*)

Fixpoint init_dist_aux (nodes: list(node)) (dist_list : list(node*nat)) 
 : list (node*nat) :=
   match nodes with 
    | [] => dist_list
    | h :: t => init_dist_aux t dist_list ++ [(h, 1000)]
end.

Definition init_dist 
(graph: list(node * (list (node*nat)))) : list(node*nat) :=
  init_dist_aux (all_nodes graph) [].

Compute (init_dist customGraph).


Example test_init_dist: (init_dist customGraph)= [(Node 9, 1000); (Node 8, 1000); 
       (Node 7, 1000); (Node 6, 1000); (Node 5, 1000);
       (Node 1, 1000); (Node 2, 1000); (Node 3, 1000);
       (Node 4, 1000)].
Proof.
  reflexivity.
Qed.


(* 
Function to update vlaue in dist node_pair_list.

The values in dist node_pair_list is only updated if it is less than the value already seen.

Function name: update_dist

*)
Fixpoint update_dist_aux 
(old_dist: list(node*nat))
(query_node: node)
(value : nat)
(seen : list(node*nat))
: list(node*nat) :=
  match old_dist with
  | [] => seen
  | h :: t => match is_equal (fst h) query_node with
              | true => match (ltb value (snd h)) with
                        | true => seen ++ [(fst h, value)] ++ t
                        | false => seen ++ old_dist
                        end
              | false => update_dist_aux t query_node value (seen ++ [h])
              end
  end.

(* Only updates the dist if the value is smaller *)

Definition update_dist
(dist: list(node*nat)) (*The dist to be updated *)
(query_node : node) (* The node whose distance is to be updated *)
(value: nat) : list(node*nat) :=
  update_dist_aux dist query_node value [].


Fixpoint update_neigh_dist
  (neigh_list : list(node*nat))
  (dist: list(node*nat))
  (cur_fuel: nat) : list(node*nat) :=
      match neigh_list with
      | [] => dist
      | h :: t => 
          let query_node := (fst h) in
          let new_val := cur_fuel + (snd h) in
          let new_dist := update_dist dist query_node new_val in
            update_neigh_dist t new_dist cur_fuel
end.

Fixpoint Dijsktra_aux
  (graph: list(node * (list (node * nat)))) 
  (dist : list(node*nat))
  (Q : list(node)) (* this becomes a counter then *)
  (visited_dist : list(node*nat))
  (cur_node : node)
    : list (node*nat)
 :=
  match Q with
  | h :: t =>   
      let cur_fuel := get_val_npl dist cur_node in
      let neigh_list := get_neigh graph cur_node in
      let dist_updated := update_neigh_dist neigh_list dist cur_fuel in
      let new_visited_dist := visited_dist ++ [(cur_node, cur_fuel)] in
      let new_dist :=  remove_node_npl dist_updated cur_node in
      let new_cur_node :=  fst (get_smallest_npl new_dist) in 
          Dijsktra_aux graph new_dist t new_visited_dist new_cur_node 
   | [] => visited_dist
end.

Definition Dijkstra
(graph: list(node * (list (node * nat))))
(src : node) : list(node*nat) := 
  let dist := init_dist graph in
  let new_dist := update_dist dist src 0 in
  let Q := all_nodes graph in
  Dijsktra_aux graph new_dist Q [] src.

Compute (Dijkstra customGraph (Node 1)).

Definition graph_ex1 := 
  [
    (Node 1, [ (Node 2,3); (Node 3,1)] );
    (Node 2, [ (Node 3,7); (Node 4,5); (Node 5,1)] );
   (Node 3, [(Node 4,2)]);
    (Node 4, [(Node 2,5); (Node 5, 7)])].


Compute (Dijkstra graph_ex1 (Node 1)).



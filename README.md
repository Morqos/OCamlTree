# OCamlTree
A basic interpreter with Trees as a type

### Requirements
OCaml compiler: [Installation](https://ocaml.org/docs/install.html)

### To Execute
From terminal:
* `git clone https://github.com/Morqos/OCamlTree.git`
* `cd OCamlTree`
* `ocaml < tree.ml`

### About the source
Primitive types and trees represented as exp, the trees can be homogeneous as not homogeneous and the tree traversal's algorithm is pre-Order. <br />
Functions applied where is possible to combine the type of the node with the input type of the function. <br />
3 Operations for the trees:
- ApplyOver: Application Function to all the nodes
- Update: Application Function to selected specific Nodes
- Select: Nodes' conditional selection

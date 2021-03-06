# DPLL_propositional_logical_inference

Starting from a FNC (Conjunctive Normal Form), that is, a series of clauses (literals joined by the or operator) joined by an and operator.
Apply the DPLL algorithm and determine the values of the literals that give a solution to the FNC.  A clear explanation of the DPLL algorithm can be found at http://www.cs.us.es/~fsancho/?e=120. 

The tests have been implemented based on the examples that appear in a link to netlogo on that page.  If you have an expedition in FBC (with connectors => and &lt;=>) you can switch to an FNC, which would be the entrance to this project, downloading the https://github.com/bertuccio/inferencia-logica-proposicional project. This project can be completed with the DPLL algorithm by adding the instructions given from the definition of the DPLL function to the end. And activating the instructions that appear in the function pasa-lista-FBF-to-lista-FNC that would serve as an interface between both projects.

In fact, DPLL_propositional_logical_inference is intended to complete Inferencia Logica Proposicional, with the DPLL algorithm and share functions.

Requirements: Allegro CL 10.1 Free Express Edition 

References: 

https://github.com/bertuccio/inferencia-logica-proposicional by Adrián Lorenzo Mateo (Bertuccio) who uses material from the Artificial Intelligence practices at the Higher Polytechnic School of the Autonomous University of Madrid. Informatics Engineering.

http://www.cs.us.es/~fsancho/?e=120 by Fernando Sancho Caparrini. Higher Technical School of Computer Engineering of the University of Sevilla.

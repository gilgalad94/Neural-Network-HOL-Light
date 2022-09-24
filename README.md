# Neural-Network-HOL-Light
Demonstration of the validity of the following theorem: given a standard neural network it can popossible to implement the absolute value function in order to have two possible values belonging the state of a neuron


(* ================  Standard Neural Network with absolute value  ================== *)





prioritize_real();;





(* ================ Hopfield Neuron definition, where e = energy_function; x pow n = generic input value ; inp 1,inp2 = input; b = bias ================== *)





let hopfield_neuron = new_definition
`hopfield_neuron e ((x pow n),b) (inp1,inp2) out <=>
out = e(x pow n * inp1 + x pow n * inp2 + b):real`;;





(*========= energy function e definition: it allows to place the neuron in a "fire" condition. e.g., activation to perform a certain activity ============= *)




let energy_function = new_definition
`energy_function e = if e < &0 then &0
else &1`;;





(* =================== two-input percepetron definition: where h = activation function, w1,w2 weights  e b = bias ================== *)




let perceptron2 = new_definition
`perceptron2 h((w1,w2),b) (inp1,inp2) out <=>
out = h(w1*inp1 + w2*inp2 + b):real`;;





(* ================== hopfield_neuron application to the energy_function: the neuron is activated in order to execute a task ================= *)





 let energy_hopfield_neuron = new_definition
`energy_hopfield_neuron = hopfield_neuron energy_function`;;





 (* proof that hopfield_neuron = perceptron2 *)





g `!e w b inp1 inp2 out.
     hopfield_neuron e (w,b) (inp1,inp2) out <=>
     perceptron2 e ((w,w),b) (inp1,inp2) out`;;





e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `w = w pow 1` SUBST1_TAC);;
search[`x pow 1`];;
e (REWRITE_TAC[REAL_POW_1]);;
e (REWRITE_TAC[hopfield_neuron; perceptron2]);;
let HOPFIELD_NEURON = top_thm();;





(* =============== building the standard neural network ================ *)





(* =============== one-input perceprton1 demonstration:  where r = activity function, w = weight, b = bias, r = Relu_function: which allows to process the input ================ *)





let perceptron1 = new_definition
  `perceptron1 r (w,b) inp out <=>
     out = r(w*inp + b):real`;;





(* ================== relu_function definition ================= *)





let relu_function = new_definition
  `relu_function r = if &0 <= r then r else &0`;;





(* ================ application of relu_function to perceptron1 ==================== *)






let relu_perceptron1 = new_definition
  `relu_perceptron1 = perceptron1 relu_function`;;





(* perceptron2 applicazione lineare *)





let lin_perceptron2 = new_definition
`lin_perceptron2 = perceptron2 (\x.x)`;;





(* ===================== buildng of the extended network made of one input (inp variable) and one output (out variable).The first layer is made of two perceptron relu, where the two outputs are int1, int2. The seconfìd layer is made of lin_perceptron2. And then, we have the final state. Such network can implement the absolute value function ===================== *)





g `!inp out int1 int2.
     relu_perceptron1 (-- &1, &0) inp int1 /\
     relu_perceptron1 (&1, &0) inp int2 /\
     lin_perceptron2 ((&1,&1),&0) (int1,int2) out
     ==> out = abs(inp)`;;





e (REPEAT GEN_TAC);;
e (REWRITE_TAC[relu_perceptron1; lin_perceptron2]);;
e (REWRITE_TAC[perceptron1; perceptron2; relu_function]);;
e REAL_ARITH_TAC;;
top_thm();;

# Neural-Network-HOL-Light
Demonstration of the validity of the following theorem: given a standard neural network it can possible to implement the absolute value function in order to have two possible values belonging the state of a neuron


# Getting started: HOL- Light Installation

   HOL LIGHT

HOL Light is an interactive theorem prover / proof checker. It is
written in Objective CAML (OCaml) and uses the toplevel from OCaml as
its front end. This is the HOL Light homepage:

        http://www.cl.cam.ac.uk/~jrh13/hol-light/index.html

and this is the root of the Github code repository:

        https://github.com/jrh13/hol-light

Basic installation instructions are below. For more detailed information
on usage, see the Tutorial:

        http://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf

Refer to the reference manual for more details of individual functions:

        http://www.cl.cam.ac.uk/~jrh13/hol-light/reference.html (HTML files)
        http://www.cl.cam.ac.uk/~jrh13/hol-light/reference.pdf (one PDF file)

        *       *       *       *       *       *       *       *

                             INSTALLATION

If you use Debian Linux or some other Debian-based Linux distribution
(Knoppix, Mint, Ubuntu, etc.), there is actually a "hol-light" package,
thanks to Hendrik Tews, so installation of HOL Light and all its
prerequisites is as simple as

  sudo apt-get install hol-light

For other OSs, more work is involved. The Objective CAML (OCaml)
implementation is a prerequisite for running HOL Light. HOL Light
should work with any recent version of OCaml; I've tried it on at
least 3.04, 3.06, 3.07+2, 3.08.1, 3.09.3, 3.10.0, 3.11.2 and 4.00.
However, for versions >= 3.10 (in 3.10 there was an incompatible
change in the camlp4 preprocessor) you will also need to get camlp5
(version >= 4.07). Installing both items of software should not be too
difficult, depending on the platform.

 1. OCaml: there are packages for many Linux distributions. For
    example, on a debian derivative like Ubuntu, you may just need
    to do the following:

        sudo apt-get install ocaml

    Alternatively you can download binaries directly, or get sources
    and build them (which in my experience is usually trouble-free).
    See the OCaml Web page for downloads and other information.

        http://caml.inria.fr/ocaml/index.en.html

    The HOL Light system uses the OCaml "Num" library for rational
    arithmetic. As of OCaml 4.06, this is no longer included in
    the core system and will need to be added separately. You can
    do this using the OCaml package manager "opam" if you use it by

        opam install num

    Alternatively you can download the sources from here

        https://github.com/ocaml/num

    and build and install them following the instructions on that
    page, for example

        git clone https://github.com/ocaml/num mynums
        cd mynums
        make all
        sudo make install [assuming no earlier errors]

 2. camlp5: this is needed to run HOL Light under any OCaml >= 3.10.
    Somtimes you need a recent version of camlp5 to be compatible with
    your OCaml. I recommend downloading the sources for a recent
    version from

        https://camlp5.github.io/

    and building it in "strict" mode before installing it, thus:

        cd software/camlp5-rel701 [or wherever you unpacked sources to]
        ./configure --strict
        make
        sudo make install       [assuming no earlier errors]

    There are also packages for camlp5, so you may be able to get away
    with just something like

        sudo apt-get install camlp5

    However, you may get a version in "transitional" instead of
    "strict" mode (do "camlp5 -pmode" to check which you have).

Now for HOL Light itself. The instructions below assume a Unix-like
environment such as Linux [or Cygwin (see www.cygwin.com) under
Windows], but the steps automated by the Makefile are easy enough to
invoke manually. There's more detail on doing that in the Tutorial.

(0) You can download the HOL Light sources from the Github site.
    For example, the following will copy the code from the trunk of the
    Github repository into a new directory 'hol-light':

        git clone https://github.com/jrh13/hol-light.git

    The above is now the recommended way of getting HOL Light. There
    are also gzipped tar files on the HOL Light Web page, but they are
    only for quite old versions and will probably be difficult to use
    with recent versions of OCaml.

    You should next enter the 'hol-light' directory that has been
     created:

        cd ./hol-light

There are now two alternatives: launch the OCaml toplevel and directly
load the HOL Light source files into it, or create a standalone image
with all the HOL Light sources pre-loaded. The latter is more
convenient, but requires a separate checkpointing program, which may not
be available for some platforms. First the basic approach:

(1) Do 'make'. This ought to build the appropriate syntax extension
    file ('pa_j.cmo') for the version of OCaml that you're using. If you
    have the camlp4 or camlp5 libraries in a non-standard place rather
    than /usr/local/lib/ocaml/camlp4 or /usr/local/lib/ocaml/camlp5
    then you may get an error like this

      Error while loading "pa_extend.cmo": file not found in path.

    in which case you should add the right directory to CAMLP4LIB or
    CAMLP5LIB, e.g.

      export CAMLP5LIB=$HOME/mylib/ocaml/camlp5

(2) Do 'ocaml'. (Actually for OCaml >= 4.02 I prefer 'ocaml -safe-string'
    to avoid mutable strings, while you may need something else like
    'ocamlnum' on some platforms --- see [*] below.) You should see a
    prompt, something like:

                Objective Caml version 4.01.0

        #

(3) At the OCaml prompt '#', do '#use "hol.ml";;' (the '#' is part of the
    command, not the prompt) followed by a newline. This should rebuild
    all the core HOL Light theories, and terminate after a few minutes
    with the usual OCaml prompt, something like:

        val search : term list -> (string * thm) list = <fun>
        - : unit = ()
        File "help.ml" already loaded
        - : unit = ()
        - : unit = ()
        - : unit = ()
                Camlp5 parsing version 7.03

        #

    HOL Light is now ready for the user to start proving theorems. You
    can also use the load process (2) and (3) in other directories, but
    you should either set the environment variable HOLLIGHT_DIR to point
    to the directory containing the HOL source files, or change the
    first line of "hol.ml" to give that explicitly, from

        let hol_dir = ref (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;

    to, for example

        let hol_dir = "/home/johnh/hol-light";;

    or

        let hol_dir = "/usr/share/hol";;

Now for the alternative approach of building a standalone image.
The level of convenience depends on the checkpointing program you
have installed. The earlier checkpointing programs in this list
are more convenient to use but seem less easy to get going on
recent Linux kernel/libc combinations.

(1) If you have the 'ckpt' program installed, then the Makefile will
    conveniently create a HOL Light binary. You can get 'ckpt' here:

        http://www.cs.wisc.edu/~zandy/ckpt/

    Once 'ckpt' is installed, simply type

        make hol

    in the 'hol-light' directory, and a standalone HOL Light image
    called 'hol' should be created. If desired you can move or copy
    this to some other place such as '~/bin' or '/usr/local/bin'. You
    then simply type 'hol' (or './hol') to start the system up and
    start proving theorems.

    Note that although the HOL binary will work on its own, it
    does not pre-load all the source files. You will probably want
    to keep the sources available to be loaded later as needed (if
    you need additional mathematical theories or tools), so it's
    better to unpack the HOL distribution somewhere permanent
    before doing 'make hol'.

    If you later develop a large body of proofs or tools, you can
    save the augmented system using the command "self_destruct"
    (this is the same approach as in the Makefile) rather than
    re-load each time. For example, the following will create a
    HOL Light binary (always called 'hol.snapshot'):

        self_destruct "My version of HOL Light";;

(2) Another checkpointing option is CryoPID, which you can get
    here:

        http://cryopid.berlios.de/

    In this case, the Makefile doesn't have a convenient way of
    making HOL binaries, but you can make one yourself once HOL
    Light is loaded and you are sitting in its toplevel loop.
    (This also works if you have your own extensions loaded, and
    indeed this is when it's most useful.) Instead of the
    'self_destruct' command, use 'checkpoint', which is similar
    except that the current process is not terminated once the
    binary (again called hol.snapshot) is created:

        checkpoint "My version of HOL Light";;

(3) A third option which seems to work with recent Linuxes is
    DMTCP, which you can download from here:

      http://dmtcp.sourceforge.net/

    You may try installing from the packages (e.g.
    'sudo dpkg -i dmtcp.deb'), but I found it was better to
    compile from source. HOL Light does not have convenient
    commands or scripts to exploit DMTCP, but you can proceed
    as follows:

        1. Start ocaml running under the DMTCP coordinator:

              dmtcp_checkpoint -n ocaml

        2. Use ocaml to load HOL Light as usual, for example:

              #use "hol.ml";;

        3. From another terminal, issue the checkpoint command:

             dmtcp_command --checkpoint

        4. (Don't forget this!) Kill the original ocaml process,
           e.g. by just typing control-d to the Ocaml prompt.

        5. Step 3 created a checkpoint of the OCaml process and
           a shell script to invoke it, both in the directory in
           which ocaml was started. Running that should restore
           the OCaml process with all your state and bindings:

             ./dmtcp_restart_script.sh

(4) If none of these options work, you may find some others on the
    following Web page. Unfortunately I don't know of any such
    checkpointing program for either Windows or Mac OS X; I would
    be glad to hear of one.

        http://checkpointing.org

The directories "Library" and "Examples" may give an idea of the
kind of thing that might be done, or may be useful in further work.

Thanks to Carl Witty for help with Camlp4 porting and advice on
checkpointing programs.

        *       *       *       *       *       *       *       *

[*] HOL Light uses the OCaml 'num' library for multiple-precision
rationals. On many platforms, including Linux and native Windows, this
will be loaded automatically by the HOL root file 'hol.ml'. However,
OCaml on some platforms (notably Cygwin) does not support dynamic
loading, hence the need to use 'ocamlnum', a toplevel with the 'num'
library already installed. You can make your own with:

    ocamlmktop -o ocamlnum nums.cma
Footer
?? 2022 GitHub, Inc.
Footer navigation
Terms


# Let's Begin

(* Standard Neural Network with absolute value *)





prioritize_real();;





(* Hopfield Neuron definition, where e = energy_function; x pow n = generic input value ; inp 1,inp2 = input; b = bias *)





let hopfield_neuron = new_definition
`hopfield_neuron e ((x pow n),b) (inp1,inp2) out <=>
out = e(x pow n * inp1 + x pow n * inp2 + b):real`;;





(* energy function e definition: it allows to place the neuron in a "fire" condition. e.g., activation to perform a certain activity *)




let energy_function = new_definition
`energy_function e = if e < &0 then &0
else &1`;;





(* two-input perceptron definition: where h = activation function, w1,w2 weights  e b = bias *)




let perceptron2 = new_definition
`perceptron2 h((w1,w2),b) (inp1,inp2) out <=>
out = h(w1*inp1 + w2*inp2 + b):real`;;





(* hopfield_neuron application to the energy_function: the neuron is activated in order to execute a task *)





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





(* building the standard neural network *)





(* one-input perceptron1 demonstration:  where r = activity function, w = weight, b = bias, r = Relu_function: which allows to process the input *)





let perceptron1 = new_definition
  `perceptron1 r (w,b) inp out <=>
     out = r(w*inp + b):real`;;





(* relu_function definition *)





let relu_function = new_definition
  `relu_function r = if &0 <= r then r else &0`;;





(* application of relu_function to perceptron1 *)






let relu_perceptron1 = new_definition
  `relu_perceptron1 = perceptron1 relu_function`;;





(* perceptron2 linear application *)





let lin_perceptron2 = new_definition
`lin_perceptron2 = perceptron2 (\x.x)`;;





(* building the extended network made of one input (inp variable) and one output (out variable).The first layer is made of two perceptron relu, where the two outputs are int1, int2. The second layer is made of lin_perceptron2. And then, we have the final state. Such network can implement the absolute value function *)





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

# Machine Proof of the Axiom of Choice and Its Equivalent Propositions(Depends on older versions of MK)  选择公理及其等价命题的机器证明(依赖于旧版本MK)
The axiom of choice is an axiom about the existence of mappings in set theory. It was first proposed by Zermelo in 1904 and used to prove the well-ordering theorem. The axiom of choice plays an important role in modern mathematics and is closely related to many profound mathematical conclusions. Without the axiom of choice, it is even impossible to determine whether two sets can compare the number of elements, whether the product of non-empty sets is non-empty, whether a linear space must have a set of bases, whether a ring must have a maximal ideal, etc. The axiom of choice has multiple equivalent theorems, including Tukey's lemma, Hausdorf's maximum principle, Zermelo's assumption, Zorn's lemma, and the well-ordering theorem. The important Tychonoff product theorem in topology is a more profound application of the axiom of choice.
Starting from the axiom of choice, we prove Tukey's lemma, Hausdorff's maximum principle, the maximum principle, Zermelo's assumption, Zorn's lemma, and the well-ordering theorem in turn, and then regard the axiom of choice as a theorem, which is respectively represented by Tukey's lemma, Zermelo's maximum principle, Zorn's lemma, and the well-ordering theorem. Assumptions and the well-ordered theorem prove the axiom of choice, completing the proof of the entire cycle strategy, thus showing that the above propositions are equivalent to the axiom of choice. The manual proof process of these propositions is standard and can be found in related monographs or textbooks on topology or set theory.

This version of the code is iteratively generated based on the old version. 
https://github.com/styzystyzy/Axiom_of_Choice

选择公理是集合论里有关映射存在性的一条公理,最早于1904年由Zermelo提出,并用于对良序定理的证明,选择公理在现代数学中有很重要的作用,与许多深刻的数学结论有着十分密切的联系,没有选择公理,甚至无法确定两个集合能否比较元素的多少、非空集的积是否非空、线性空间是否一定有一组基、环是否一定有极大理想等等.选择公理有多个等价定理,包括Tukey引理、Hausdorf 极大原则、Zermelo 假定、Zorn 引理、良序定理等.拓扑学中重要的 Tychonoff 乘积定理即选择公理较为深刻的一个应用.
我们从选择公理出发,依次证明 Tukey引理、Hausdorff 极大原则、极大原则、Zermelo 假定、Zorn 引理和良序定理,再将选择公理视为一条定理,分别由 Tukey 引理、Zermelo 假定及良序定理证明选择公理,完成整个循环策略的证明,从而说明上述各命题与选择公理等价，这些命题的人工证明过程是标准的，散见于拓扑学或集合论的相关专著或教材中.

本版代码基于旧版本迭代而来 
https://github.com/styzystyzy/Axiom_of_Choice
# Files
The proof is based on Morse-Kelley axiomatic set theory(Depends on older versions of MK), which includes the following twelve .v files:

A_0.v  

A_1.v   (*Depends on A_0.v *)

A_2.v   (*Depends on A_1.v *)

A_3.v   (*Depends on A_2.v *)

A_4.v   (*Depends on A_3.v *)

A_5.v   (*Depends on A_4.v *)

A_6.v   (*Depends on A_5.v *)

A_7.v   (*Depends on A_6.v *)

A_8.v   (*Depends on A_7.v *)

A_9.v   (*Depends on A_8.v *)

A_10.v   (*Depends on A_9.v *)

A_11.v   (*Depends on A_10.v *)

The machine proof of the axiom of choice and its equivalent propositions itself includes the following 10 .v files:

Basic_Definitions.v -- Basic definitions required for the proof. (* Depends on A_11.v *)

Tukey_Lemma.v -- Prove Tukey_Lemma through the Axiom of Choice. (* Depends on Basic_Definitions.v *)

Hausdorff_Maximal_Principle.v -- Prove Hausdorff_Maximal_Principle through Tukey_Lemma.  (* Depends on Tukey_Lemma.v *)

Maximal_Principle.v -- Prove Maximal_Principle through Hausdorff_Maximal_Principle.  (* Depends on Hausdorff_Maximal_Principle.v *)

Zorn_Lemma.v -- Prove Zorn_Lemma through Maximal_Principle.  (* Depends on Maximal_Principle.v *)

Wellordering_Theorem.v -- Prove Wellordering_Theorem through Zorn_Lemma.  (* Depends on Zorn_Lemma.v *)

WO_Proof_AC.v -- Prove the Axiom of Choice through Wellordering_Theorem.  (* Depends on Wellordering_Theorem.v *)

Zermelo_Postulate.v -- Prove Zermelo_Postulate through Maximal_Principle.  (* Depends on Maximal_Principle.v *)

Zermelo_Proof_AC.v -- Prove the Axiom of Choice through Zermelo_Postulate.  (* Depends on Zermelo_Postulate.v *)

Tukey_Proof_AC.v -- Prove the Axiom of Choice through Tukey_Lemma.  (* Depends on Tukey_Lemma.v *)
# Authors
This project is implemented by Wensheng Yu wsyu@bupt.edu.cn、Tianyu Sun、Yaoshun Fu、Sheng Yan、Si Chen、Ce Zhang.
# Relevant Papers & Books
Yu, W., Sun, T., Fu, Y.: A Machine Proof System for Axiomatic Set Theory (in Chinese). Science Press, Beijing (2020)

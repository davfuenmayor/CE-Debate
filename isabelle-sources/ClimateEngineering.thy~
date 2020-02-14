(*<*)
theory ClimateEngineering
imports embedding
begin
(* Configuration defaults *)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)
(*>*)

section\<open>Case Study: Arguments in the Climate Engineering Debate\<close>
(**
Formalisation and evaluation of an extract of the argument network presented by Gregor Betz and
Sebastian Cacean in their work "Ethical Aspects of Climate Engineering", freely available for download at: 
http://books.openedition.org/ksp/pdf/1780
*)

subsection\<open>Individual (Component) Arguments\<close>
(**The arguments below primarily support the thesis: "CE deployment is morally wrong"
and make for an argument cluster with a non-trivial dialectical structure which we aim at
reconstructing in this section. We focus on six arguments from the ethics of risk,
which entail that the deployment of CE technologies (today as in the future) is not desirable
because of being morally wrong (argument A22). Supporting arguments of A22 are: A45, A46, A47, A48, A49.
In particular, two of these arguments, namely A47 and A49, are further attacked by A50 and A51.
*)

subsubsection\<open>Ethics of Risk Argument (A22)\<close>
(**The argument has as premise T9: "CE deployment is morally wrong" and as conclusion:
"CE deployment is not desirable". Notice that both are formalised as (modally) valid propositions,
i.e. true in all possible worlds or situations. We are thus presupossing a possible-worlds semantics.*)

consts CEisWrong::"w\<Rightarrow>bool"  (**notice type for world-contingent propositions*)
       CEisNotDesirable::"w\<Rightarrow>bool"
definition A22_P1::bool where "A22_P1 \<equiv> [\<turnstile> CEisWrong]" (*(aka. T9) CE is wrong in all situations*)
definition A22_P2::bool where "A22_P2 \<equiv> [\<turnstile> CEisWrong \<^bold>\<rightarrow> CEisNotDesirable]" (*implicit!*)
definition A22_C::bool where "A22_C \<equiv> [\<turnstile> CEisNotDesirable]" (*...also in all situations*)

(**We use Nitpick to find a model satisfying the premises and the conclusion of the formalised argument.*)
lemma assumes A22_P1 and A22_P2 and A22_C shows True 
  nitpick [satisfy] oops (**consistency is shown: nitpick presents a simple model*)

theorem A22_valid: assumes A22_P1 and A22_P2 shows A22_C
  using A22_C_def A22_P2_def A22_P1_def assms(1) assms(2) by blast

subsubsection\<open>Termination Problem (A45)\<close>
(**CE measures do not possess viable exit options. If deployment is terminated abruptly,
catastrophic climate change ensues.
*)
consts CEisTerminated::"w\<Rightarrow>bool"   (**world-contingent propositional constants*)
       CEisCatastrophic::"w\<Rightarrow>bool"
definition A45_P1::bool where "A45_P1 \<equiv> [\<turnstile> \<^bold>\<diamond>CEisTerminated]"
definition A45_P2::bool where "A45_P2 \<equiv> [\<turnstile> CEisTerminated \<^bold>\<rightarrow> CEisCatastrophic]"
definition A45_C::bool  where  "A45_C \<equiv> [\<turnstile> \<^bold>\<diamond>CEisCatastrophic]"

(**Notice that we have introduced in the above formalisation the @{text "\<diamond>"}
modal operator to signify that a proposition is possibly true (e.g. at a future point in time).*)
theorem A45_valid: assumes A45_P1 and A45_P2 shows "A45_C"
  using A45_C_def A45_P1_def A45_P2_def assms(1) assms(2) by blast

subsubsection\<open>No Long-term Risk Control (A46)\<close>
(**Our social systems and institutions are possibly not capable of controlling risk technologies
on long time scales and of ensuring that they are handled with proper technical care.
Notice that we can make best sense of this objection as (implicitly?) presupossing a risk of 
CE-caused catastrophes.*)

consts RiskControlAbility::"w\<Rightarrow>bool"
definition A46_P1::bool where "A46_P1 \<equiv> [\<turnstile> \<^bold>\<diamond>\<^bold>\<not>RiskControlAbility]"
definition A46_P2::bool where "A46_P2 \<equiv> [\<turnstile> \<^bold>\<not>RiskControlAbility \<^bold>\<rightarrow> \<^bold>\<diamond>CEisCatastrophic]"
definition A46_C::bool where   "A46_C \<equiv> [\<turnstile> \<^bold>\<diamond>CEisCatastrophic]"

(**The argument A46 needs a modal logic "K4" to succeed.
The implicit premise thus being:  @{text "Ax4: [\<turnstile> \<forall>\<phi>. \<box>\<box>\<phi> \<rightarrow> \<box>\<phi>]"}. *)
lemma assumes A46_P1 and A46_P2 shows A46_C
  nitpick oops (**counterexample found, since modal axiom 4 is needed here*)
theorem A46_valid: assumes A46_P1 and A46_P2 and Ax4 shows A46_C
  using A46_C_def A46_P1_def A46_P2_def assms(1) assms(2) assms(3) by blast

subsubsection\<open>CE Interventions are Irreversible (A47)\<close>
(**This argument consists of a simple sentence (its conclusion), which
states that CE represents an irreversible intervention, i.e., that once the first
interventions on world's climate have been set in motion, there is no way to "undo" them. 
For the following arguments we work with a predicate logic (incl. quantification), and
thus introduce a type ("e") for actions (interventions).*)

typedecl e (**introduces a new type for actions*)
consts CEAction::"e\<Rightarrow>w\<Rightarrow>bool" (**notice type for (world-dependent) predicates*)
       Irreversible::"e\<Rightarrow>w\<Rightarrow>bool" 
definition A47_C::bool where "A47_C \<equiv> [\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> Irreversible(I)]"

subsubsection\<open>No Ability to Retain Options after Irreversible Interventions (A48)\<close>
(**Irreversible interventions (of any kind) narrow the options of future generations in an unacceptable way,
i.e., it is wrong to carry them out.*)

consts WrongAction::"e\<Rightarrow>w\<Rightarrow>bool"
definition A48_C::bool where "A48_C \<equiv> [\<turnstile> \<^bold>\<forall>I. Irreversible(I) \<^bold>\<rightarrow> WrongAction(I)]"

subsubsection\<open>Unpredictable Side-Effects are Wrong (A49)\<close>
(**As long as side-effects of CE technologies cannot be reliably predicted,
their deployment is morally wrong.*)

consts USideEffects::"e\<Rightarrow>w\<Rightarrow>bool"
definition A49_P1::bool where "A49_P1 \<equiv> [\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> USideEffects(I)]"
definition A49_P2::bool where "A49_P2 \<equiv> [\<turnstile>\<^bold>\<forall>I. USideEffects(I) \<^bold>\<rightarrow> WrongAction(I)]"
definition A49_C ::bool where "A49_C  \<equiv> [\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)]"

theorem A49_valid: assumes A49_P1 and A49_P2 shows A49_C (*blast verifies validity*)
  using A49_C_def A49_P1_def A49_P2_def assms(1) assms(2) by blast

subsubsection\<open>Mitigation is also Irreversible (A50)\<close>
(**Mitigation of climate change (i.e., the "prevention" alternative to CE), too, is, at least to some
extent, an irreversible intervention with unforeseen side-effects.*)

consts Mitigation::e (**constant of same type as actions/interventions*)
definition A50_C::bool where 
  "A50_C \<equiv> [\<turnstile> Irreversible(Mitigation) \<^bold>\<and> USideEffects(Mitigation)]"

subsubsection\<open>All Interventions have Unpredictable Side-Effects (A51)\<close>
(**This defense of CE states that we do never completely foresee the consequences of our actions anyways,
and thus aims at somehow trivializing the concerns regarding unforeseen side-effects of CE.*)

definition A51_C where "A51_C \<equiv> [\<turnstile> \<^bold>\<forall>I. USideEffects(I)]"

subsection\<open>Reconstructing the Argument Graph\<close>
(**Below we introduce our generalized attack/support relations between arguments.*)

abbreviation attacks1 where  "attacks1 \<phi> \<psi>  \<equiv> (\<phi> \<and> \<psi>) \<longrightarrow> False" (**one attacker*)
abbreviation supports1 where "supports1 \<phi> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>" (**only one supporter*)
abbreviation attacks2 where  "attacks2 \<gamma> \<phi> \<psi>  \<equiv> (\<gamma> \<and> \<phi> \<and> \<psi>) \<longrightarrow> False" (*two attackers *)
abbreviation supports2 where "supports2 \<gamma> \<phi> \<psi> \<equiv> (\<gamma> \<and> \<phi>) \<longrightarrow> \<psi>" (**two supporters*)

subsubsection\<open>Does A45 support A22?\<close>
(**Implicit premise needed.*)
lemma "supports1 A45_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  shows "supports1 A45_C A22_P1" using A22_P1_def A45_C_def assms(1) by blast

subsubsection\<open>Does A46 support A22?\<close>
(**The same implicit premise as before is needed.*)
lemma "supports1 A46_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<diamond>CEisCatastrophic \<^bold>\<rightarrow> CEisWrong]" (**implicit*)
  shows "supports1 A46_C A22_P1" using A22_P1_def A46_C_def assms(1) by blast

subsubsection\<open>Do A47 and A48 (together) support A22?\<close>
(**Implicit premise again needed.*)
lemma "supports2 A47_C A48_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile>\<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)]\<longrightarrow>[\<turnstile> CEisWrong]" (*implicit*)
  shows "supports2 A47_C A48_C A22_P1"
  using A22_P1_def A47_C_def A48_C_def assms(1) by blast (**assms(1) implicit*)

subsubsection\<open>Does A49 support A22?\<close>
(**An implicit premise is also needed.*)
lemma "supports1 A49_C A22_P1" nitpick oops (**countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<rightarrow> WrongAction(I)] \<longrightarrow> [\<turnstile> CEisWrong]"
  shows "supports1 A49_C A22_P1" using A22_P1_def A49_C_def assms(1) by blast

subsubsection\<open>Does A50 attack both A47 and A49?\<close>
(**Here, too, are two additional implicit premises needed.*)
lemma "attacks1 A50_C A47_C" nitpick oops (** countermodel found*)
lemma "attacks1 A50_C A49_C" nitpick oops (** countermodel found*)

theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**second implicit premise*)
  shows "attacks2 A48_C A50_C A47_C"
  using A47_C_def A48_C_def A50_C_def assms(1) assms(2) by fastforce
theorem assumes "[\<turnstile> \<^bold>\<forall>I. CEAction(I) \<^bold>\<or> (I \<^bold>\<approx> Mitigation)]" (**first implicit premise*)
  and "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**second implicit premise*)
  shows "attacks2 A50_C A49_P1 A49_P2"
  using A49_P1_def A49_P2_def A50_C_def assms(1) assms(2) by fastforce

subsubsection\<open>Does A51 attack A49?\<close>
(**The same implicit premise as before is needed.*)
lemma "attacks2 A51_C A49_P1 A49_P2" nitpick oops (** countermodel found*)
theorem assumes "[\<turnstile> \<^bold>\<exists>I. \<^bold>\<not>WrongAction(I)]" (**implicit premise *)
  shows "attacks1 A51_C A49_P2" using A49_P2_def A51_C_def assms(1) by blast

(*<*)
end
(*>*)
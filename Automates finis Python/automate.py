#Lorie XUE : 28705252
#Cyril LIN : 28633410
#L2 DANT 


# -*- coding: utf-8 -*-
import itertools
from re import A, I
from transition import *
from state import *
import os
import copy
from itertools import product
from automateBase import AutomateBase



class Automate(AutomateBase):
        
    def succElem(self, state, lettre):
        """State x str -> list[State]
        rend la liste des états accessibles à partir d'un état
        state par l'étiquette lettre
        """
        successeurs = []
        # t: Transitions
        for t in self.getListTransitionsFrom(state):
            if t.etiquette == lettre and t.stateDest not in successeurs:
                successeurs.append(t.stateDest)
        return successeurs


    def succ (self, listStates, lettre):
        """list[State] x str -> list[State]
        rend la liste des états accessibles à partir de la liste d'états
        listStates par l'étiquette lettre
        """
        res = []

        for s in listStates :
            for su in self.succElem(s,lettre) :
                if not su in res : 
                    res.append(su)
        return res




    """ Définition d'une fonction déterminant si un mot est accepté par un automate.
    Exemple :
            a=Automate.creationAutomate("monAutomate.txt")
            if Automate.accepte(a,"abc"):
                print "L'automate accepte le mot abc"
            else:
                print "L'automate n'accepte pas le mot abc"
    """
    @staticmethod
    def accepte(auto,mot) :
        """ Automate x str -> bool
        rend True si auto accepte mot, False sinon
        """
        init = auto.getListInitialStates()
        final = auto.getListFinalStates()
        for m in mot :
            init = auto.succ(init,m)

        for f in final :
            if f in init :
                return True

        return False


    @staticmethod
    def estComplet(auto,alphabet) :
        """ Automate x str -> bool
         rend True si auto est complet pour alphabet, False sinon
        """
        state = auto.listStates
        for s in state :
            for a in alphabet :

                b = False

                for t in auto.getListTransitionsFrom(s) :
                     
                    if t.etiquette==a : 
                        b = True
                        break

                if not b :
                    return False
                    
                
        return True


        
    @staticmethod
    def estDeterministe(auto) :
        """ Automate  -> bool
        rend True si auto est déterministe, False sinon
        """
        etiquette =[] 
        if (len(auto.getListInitialStates())!=1) :
            return False
        
        for s in auto.listStates :
            for t in auto.getListTransitionsFrom(s) :
                if (t.etiquette in etiquette) :
                    return False
                etiquette.append(t.etiquette)
            
            etiquette = []

        return True
        

       
    @staticmethod
    def completeAutomate(auto,alphabet) :
        """ Automate x str -> Automate
        rend l'automate complété d'auto, par rapport à alphabet
        """
        if Automate.estComplet(auto,alphabet) :
            return copy.deepcopy(auto)
        
        auto2 = copy.deepcopy(auto)
        puit = State(len(auto.listStates), False,False,label = "P")

        for s in auto.listStates :
            alphatemp = []
            for t in auto.getListTransitionsFrom(s) :
                if not t.etiquette in alphatemp :
                    alphatemp.append(t.etiquette)
                
            if (len(alphatemp)!=len(alphabet)) :
                
                for a in alphabet :
                    auto2.addTransition(Transition(puit,a,puit))
                    if not a in alphatemp :
                        auto2.addState(puit)
                        auto2.addTransition(Transition(s,a,puit))
                    
        return auto2



    @staticmethod
    def determinisation(auto) :
        """ Automate  -> Automate
        rend l'automate déterminisé d'auto
        """
        auto2 = Automate([])
        ls = auto2.listStates
        li = auto.getListInitialStates()
        tab = [li]
        index = 0
        ef = False

        if(State.isFinalIn(li)):
            ef = True

        etat1 = State(index, True, ef,set(auto.getListInitialStates()))
        auto2.addState(etat1)

        index += 1
        estdedans = []
        estdedans.append(set(auto.getListInitialStates()))
        
        while (tab):
            for ele in tab:
                for lettre in auto.getAlphabetFromTransitions() :
                    suivant = auto.succ(ele,lettre)
                    ens_suivant = set(suivant)
                    ef = False
                    if(not suivant):
                        continue
                    
                    if(not ens_suivant in estdedans):

                        estdedans.append(ens_suivant)
                        if(State.isFinalIn(suivant)):
                            ef = True
                        auto2.addState(State(index,False,ef,ens_suivant))
                        index+=1
                        tab.append(suivant)

                    for i in range(len(estdedans)):
                            if(estdedans[i]==ens_suivant):
                                for j in range(len(estdedans)):
                                    if(estdedans[j]==set(ele)):
                                        auto2.addTransition(Transition(ls[j],lettre,ls[i]))
                                        break
                tab.remove(ele)
                
        return auto2
        
    @staticmethod
    def complementaire(auto,alphabet):
        """ Automate -> Automate
        rend  l'automate acceptant pour langage le complémentaire du langage de a
        """
        
        auto2 = Automate.determinisation(auto)
        auto3 = Automate.completeAutomate(auto2,alphabet)

        State_fin = auto3.getListFinalStates()

        for s in auto3.listStates :
            if s in State_fin :
                s.fin = False
            else :
                s.fin = True 

        return auto3


              
   
    @staticmethod
    def intersection (auto0, auto1):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage l'intersection des langages des deux automates
        """
        auto2 = Automate([])
        ls = auto2.listStates
        
        li0 = auto0.getListInitialStates()
        lf0 = auto0.getListFinalStates()
        li1 = auto1.getListInitialStates()
        lf1 = auto1.getListFinalStates()
        li = list(itertools.product(li0,li1))
        lf = list(itertools.product(lf0,lf1))
        
        alphabet0 = auto0.getAlphabetFromTransitions()
        alphabet1 = auto1.getAlphabetFromTransitions()
        if (len(alphabet0)<len(alphabet1)) :
            alphabet0 = alphabet1
        else :
            alphabet1 = alphabet0

        tab = li
        index = 0
        ef = False
        estdedans = []

        for couple in tab :
            if(couple in lf):
                ef = True
            etat1 = State(index, True, ef,couple)
            auto2.addState(etat1)
            index += 1
            estdedans.append(couple)
        
        while (tab):
            for ele in tab:
                for lettre in alphabet0 :
                    suivant0 = auto0.succElem(ele[0],lettre)
                    suivant1= auto1.succElem(ele[1],lettre)
                    suivant = list(itertools.product(suivant0,suivant1))

                    ef = False

                    if(not suivant):
                        continue
                    
                    for couple in suivant :
                        if(not couple in estdedans):
                            estdedans.append(couple)
                            
                            if(couple in lf):
                                ef = True

                            auto2.addState(State(index,False,ef,couple))
                            index+=1
                            tab.append(couple)
                        for i in range(len(estdedans)):
                                if(estdedans[i]==couple):
                                    for j in range(len(estdedans)):
                                        if(estdedans[j]==ele):
                                            auto2.addTransition(Transition(ls[j],lettre,ls[i]))
                                            break
                tab.remove(ele)
        return auto2

    @staticmethod
    def union (auto0, auto1):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage l'union des langages des deux automates
        """
        auto2 = Automate([])
        ls = auto2.listStates
        
        li0 = auto0.getListInitialStates()
        lf0 = auto0.getListFinalStates()
        li1 = auto1.getListInitialStates()
        lf1 = auto1.getListFinalStates()
        li = list(itertools.product(li0,li1))
        
        
        alphabet0 = auto0.getAlphabetFromTransitions()
        alphabet1 = auto1.getAlphabetFromTransitions()
        if (len(alphabet0)<len(alphabet1)) :
            alphabet0 = alphabet1
        else :
            alphabet1 = alphabet0

        tab = li
        index = 0
        ef = False
        estdedans = []

        for couple in tab :
            if(couple[0] in lf0 or couple[1] in lf1):
                ef = True
            etat1 = State(index, True, ef,couple)
            auto2.addState(etat1)
            index += 1
            estdedans.append(couple)
        
        while (tab):
            for ele in tab:
                for lettre in alphabet0 :
                    suivant0 = auto0.succElem(ele[0],lettre)
                    suivant1= auto1.succElem(ele[1],lettre)
                    suivant = list(itertools.product(suivant0,suivant1))

                    ef = False

                    if(not suivant):
                        continue
                    
                    for couple in suivant :
                        if(not couple in estdedans):
                            estdedans.append(couple)
                            
                            if(couple[0] in lf0 or couple[1] in lf1):
                                ef = True
                            auto2.addState(State(index,False,ef,couple))
                            index+=1
                            tab.append(couple)
                        for i in range(len(estdedans)):
                                if(estdedans[i]==couple):
                                    for j in range(len(estdedans)):
                                        if(estdedans[j]==ele):
                                            auto2.addTransition(Transition(ls[j],lettre,ls[i]))
                                            break
                tab.remove(ele)
        return auto2
        

   
    @staticmethod
    def concatenation (auto1, auto2):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage la concaténation des langages des deux automates
        """
        autoA1 = (copy.deepcopy(auto1))
        autoA2 = (copy.deepcopy(auto2))
        autoA1.prefixStates(1)
        autoA2.prefixStates(2)
        autoA2init = []
        autoA1Fin = []

        for i in range(len(autoA1.listStates)) :
            if autoA1.listStates[i].fin == True :
                autoA1.listStates[i].fin = False
                autoA1Fin.append(autoA1.listStates[i])
                
        auto3initial = autoA1.getListInitialStates()

        if not State.isFinalIn(autoA1.getListInitialStates()) :
            for i in range(len(autoA2.listStates)) :
                if autoA2.listStates[i].init == True :
                    autoA2.listStates[i].init = False
                    autoA2init.append(autoA2.listStates[i])
        else :
            auto3initial+= autoA2.getListInitialStates()
        
        auto3States = autoA1.listStates + autoA2.listStates
        auto3Transitions = autoA1.listTransitions + autoA2.listTransitions
        
        if State.isFinalIn(autoA1.getListInitialStates()) :
            auto3initial += autoA2.getListInitialStates() 

        for t in autoA1.listTransitions :
            if t.stateDest in autoA1Fin :
                for init in autoA2init :
                    auto3Transitions.append(Transition(t.stateSrc, t.etiquette ,init))

        return Automate(auto3Transitions, auto3States)
        
       
    @staticmethod
    def etoile (auto):
        """ Automate  -> Automate
        rend l'automate acceptant pour langage l'étoile du langage de a
        """
        autoinitial = auto.getListInitialStates()
        
        for i in auto.getListInitialStates() :
            i.fin = True

        
        auto2 = Automate(auto.listTransitions, autoinitial)
        auto2final = auto.getListFinalStates()
        auto2init = auto.getListInitialStates()
        
        listVersFinal = []

        for t in auto.listTransitions :   
            if t.stateSrc in auto2init :
                listVersFinal.append((t.etiquette,t.stateDest))
        
        for etiquette,stateDest in listVersFinal :
            for f in auto2final :
                if not Transition(f,etiquette,stateDest) in auto.listTransitions :
                    auto2.addTransition(Transition(f,etiquette,stateDest))
                

        return auto2


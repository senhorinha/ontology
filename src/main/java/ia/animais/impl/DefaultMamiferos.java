package ia.animais.impl;

import ia.animais.*;

import java.util.Collection;

import org.protege.owl.codegeneration.WrappedIndividual;
import org.protege.owl.codegeneration.impl.WrappedIndividualImpl;
import org.protege.owl.codegeneration.inference.CodeGenerationInference;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;


/**
 * Generated by Protege (http://protege.stanford.edu).<br>
 * Source Class: DefaultMamiferos <br>
 * @version generated on Thu May 07 17:00:01 BRT 2015 by caio
 */
public class DefaultMamiferos extends WrappedIndividualImpl implements Mamiferos {

    public DefaultMamiferos(CodeGenerationInference inference, IRI iri) {
        super(inference, iri);
    }





    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#cobertoPor
     */
     
    public Collection<? extends Cobertura> getCobertoPor() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_COBERTOPOR,
                                               DefaultCobertura.class);
    }

    public boolean hasCobertoPor() {
	   return !getCobertoPor().isEmpty();
    }

    public void addCobertoPor(Cobertura newCobertoPor) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_COBERTOPOR,
                                       newCobertoPor);
    }

    public void removeCobertoPor(Cobertura oldCobertoPor) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_COBERTOPOR,
                                          oldCobertoPor);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#comportamento
     */
     
    public Collection<? extends Comportamento> getComportamento() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_COMPORTAMENTO,
                                               DefaultComportamento.class);
    }

    public boolean hasComportamento() {
	   return !getComportamento().isEmpty();
    }

    public void addComportamento(Comportamento newComportamento) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_COMPORTAMENTO,
                                       newComportamento);
    }

    public void removeComportamento(Comportamento oldComportamento) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_COMPORTAMENTO,
                                          oldComportamento);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#ehIrracional
     */
     
    public Collection<? extends Raciocinio> getEhIrracional() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_EHIRRACIONAL,
                                               DefaultRaciocinio.class);
    }

    public boolean hasEhIrracional() {
	   return !getEhIrracional().isEmpty();
    }

    public void addEhIrracional(Raciocinio newEhIrracional) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_EHIRRACIONAL,
                                       newEhIrracional);
    }

    public void removeEhIrracional(Raciocinio oldEhIrracional) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_EHIRRACIONAL,
                                          oldEhIrracional);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#ehRacional
     */
     
    public Collection<? extends Raciocinio> getEhRacional() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_EHRACIONAL,
                                               DefaultRaciocinio.class);
    }

    public boolean hasEhRacional() {
	   return !getEhRacional().isEmpty();
    }

    public void addEhRacional(Raciocinio newEhRacional) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_EHRACIONAL,
                                       newEhRacional);
    }

    public void removeEhRacional(Raciocinio oldEhRacional) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_EHRACIONAL,
                                          oldEhRacional);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#habitaMeio
     */
     
    public Collection<? extends Habitat> getHabitaMeio() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_HABITAMEIO,
                                               DefaultHabitat.class);
    }

    public boolean hasHabitaMeio() {
	   return !getHabitaMeio().isEmpty();
    }

    public void addHabitaMeio(Habitat newHabitaMeio) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_HABITAMEIO,
                                       newHabitaMeio);
    }

    public void removeHabitaMeio(Habitat oldHabitaMeio) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_HABITAMEIO,
                                          oldHabitaMeio);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#maiorQue
     */
     
    public Collection<? extends Animal> getMaiorQue() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_MAIORQUE,
                                               DefaultAnimal.class);
    }

    public boolean hasMaiorQue() {
	   return !getMaiorQue().isEmpty();
    }

    public void addMaiorQue(Animal newMaiorQue) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_MAIORQUE,
                                       newMaiorQue);
    }

    public void removeMaiorQue(Animal oldMaiorQue) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_MAIORQUE,
                                          oldMaiorQue);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#menorQue
     */
     
    public Collection<? extends Animal> getMenorQue() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_MENORQUE,
                                               DefaultAnimal.class);
    }

    public boolean hasMenorQue() {
	   return !getMenorQue().isEmpty();
    }

    public void addMenorQue(Animal newMenorQue) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_MENORQUE,
                                       newMenorQue);
    }

    public void removeMenorQue(Animal oldMenorQue) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_MENORQUE,
                                          oldMenorQue);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#respiração
     */
     
    public Collection<? extends Reproducao> getRespiração() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_RESPIRAÇÃO,
                                               DefaultReproducao.class);
    }

    public boolean hasRespiração() {
	   return !getRespiração().isEmpty();
    }

    public void addRespiração(Reproducao newRespiração) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_RESPIRAÇÃO,
                                       newRespiração);
    }

    public void removeRespiração(Reproducao oldRespiração) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_RESPIRAÇÃO,
                                          oldRespiração);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#seLocomove
     */
     
    public Collection<? extends Locomoçao> getSeLocomove() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_SELOCOMOVE,
                                               DefaultLocomoçao.class);
    }

    public boolean hasSeLocomove() {
	   return !getSeLocomove().isEmpty();
    }

    public void addSeLocomove(Locomoçao newSeLocomove) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_SELOCOMOVE,
                                       newSeLocomove);
    }

    public void removeSeLocomove(Locomoçao oldSeLocomove) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_SELOCOMOVE,
                                          oldSeLocomove);
    }


    /* ***************************************************
     * Object Property http://www.semanticweb.org/caio/ontologies/2015/3/untitled-ontology-3#seReproduz
     */
     
    public Collection<? extends Reproducao> getSeReproduz() {
        return getDelegate().getPropertyValues(getOwlIndividual(),
                                               Vocabulary.OBJECT_PROPERTY_SEREPRODUZ,
                                               DefaultReproducao.class);
    }

    public boolean hasSeReproduz() {
	   return !getSeReproduz().isEmpty();
    }

    public void addSeReproduz(Reproducao newSeReproduz) {
        getDelegate().addPropertyValue(getOwlIndividual(),
                                       Vocabulary.OBJECT_PROPERTY_SEREPRODUZ,
                                       newSeReproduz);
    }

    public void removeSeReproduz(Reproducao oldSeReproduz) {
        getDelegate().removePropertyValue(getOwlIndividual(),
                                          Vocabulary.OBJECT_PROPERTY_SEREPRODUZ,
                                          oldSeReproduz);
    }


}

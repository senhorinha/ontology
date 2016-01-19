package org.protege.owl.codegeneration.listener;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.protege.owl.codegeneration.CodeGenerationFactory;
import org.protege.owl.codegeneration.WrappedIndividual;
import org.protege.owl.codegeneration.impl.WrappedIndividualImpl;
import org.protege.owl.codegeneration.inference.CodeGenerationInference;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLAxiomChange;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyChangeListener;
import org.semanticweb.owlapi.model.OWLPropertyAssertionAxiom;

public abstract class CodeGenerationListener<X extends WrappedIndividual> implements OWLOntologyChangeListener {
	private Set<OWLNamedIndividual> signature;
	private Set<OWLNamedIndividual> handledForCreation = new TreeSet<OWLNamedIndividual>();
	private Set<OWLNamedIndividual> handledForModification = new TreeSet<OWLNamedIndividual>();
	private CodeGenerationFactory factory;
	private CodeGenerationInference inference;
	private Class<? extends X> javaInterface;
	private OWLClass type;

	public CodeGenerationListener(CodeGenerationFactory factory, Class<? extends X> javaInterface) {
		this.signature = factory.getOwlOntology().getIndividualsInSignature();
		this.factory = factory;
		this.javaInterface = javaInterface;
		this.inference = factory.getInference();
		this.type = factory.getOwlClassFromJavaInterface(javaInterface);
	}

	public abstract void individualCreated(X individual);

	public abstract void individualModified(X individual);

	public void ontologiesChanged(List<? extends OWLOntologyChange> changes) throws OWLException {
		try {
			this.reset();
			this.handleCreationEvents(changes);
			this.handleModificationEvents(changes);
		} finally {
			this.signature = this.factory.getOwlOntology().getIndividualsInSignature();
		}
	}

	private void reset() {
		this.handledForCreation.clear();
		this.handledForModification.clear();
		this.factory.flushOwlReasoner();
	}

	private void handleCreationEvents(List<? extends OWLOntologyChange> changes) {
		for (OWLOntologyChange change : changes) {
			if (change instanceof AddAxiom) {
				this.handleCreationEvent((AddAxiom) change);
			}
		}
	}

	private void handleCreationEvent(AddAxiom change) {
		for (OWLEntity e : change.getSignature()) {
			if (e instanceof OWLNamedIndividual && !this.handledForCreation.contains(e) && !this.signature.contains(e)) {
				this.handledForCreation.add((OWLNamedIndividual) e);
				if (this.inference.canAs((OWLNamedIndividual) e, this.type)) {
					WrappedIndividual wrapped = new WrappedIndividualImpl(this.inference, (OWLNamedIndividual) e);
					this.individualCreated(this.factory.as(wrapped, this.javaInterface));
				}
			}
		}
	}

	private void handleModificationEvents(List<? extends OWLOntologyChange> changes) {
		for (OWLOntologyChange change : changes) {
			if (change instanceof OWLAxiomChange) {
				this.handleModificationEvent((OWLAxiomChange) change);
			}
		}
	}

	@SuppressWarnings("rawtypes")
	private void handleModificationEvent(OWLAxiomChange change) {
		OWLAxiom axiom = change.getAxiom();
		if (axiom instanceof OWLPropertyAssertionAxiom && ((OWLPropertyAssertionAxiom) axiom).getSubject().isNamed()) {
			OWLNamedIndividual i = ((OWLPropertyAssertionAxiom) change.getAxiom()).getSubject().asOWLNamedIndividual();
			if (!this.handledForModification.contains(i) && this.inference.canAs(i, this.type)) {
				WrappedIndividual wrapped = new WrappedIndividualImpl(this.inference, i);
				this.individualModified(this.factory.as(wrapped, this.javaInterface));
			}
		}
	}

}

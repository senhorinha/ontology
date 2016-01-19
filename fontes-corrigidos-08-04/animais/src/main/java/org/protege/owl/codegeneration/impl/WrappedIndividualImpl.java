package org.protege.owl.codegeneration.impl;

import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.protege.owl.codegeneration.WrappedIndividual;
import org.protege.owl.codegeneration.inference.CodeGenerationInference;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.util.OWLEntityRemover;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.semanticweb.owlapi.util.SimpleShortFormProvider;

/**
 * @author z.khan
 *
 */
public class WrappedIndividualImpl implements WrappedIndividual {

	private OWLOntology owlOntology;
	private OWLNamedIndividual owlIndividual;
	private CodeGenerationHelper delegate;

	/**
	 * Constructor
	 * 
	 * @param inference
	 * @param iri
	 */
	public WrappedIndividualImpl(CodeGenerationInference inference, IRI iri) {
		this(inference, inference.getOWLOntology().getOWLOntologyManager().getOWLDataFactory().getOWLNamedIndividual(iri));
	}

	public WrappedIndividualImpl(CodeGenerationInference inference, OWLNamedIndividual owlIndividual) {
		this.owlOntology = inference.getOWLOntology();
		this.owlIndividual = owlIndividual;
		this.delegate = new CodeGenerationHelper(inference);
	}

	/**
	 * @return the owlOntology
	 */
	public OWLOntology getOwlOntology() {
		return this.owlOntology;
	}

	public OWLNamedIndividual getOwlIndividual() {
		return this.owlIndividual;
	}

	protected CodeGenerationHelper getDelegate() {
		return this.delegate;
	}

	/**
	 * Asserts that the individual has a particular OWL type.
	 */

	public void assertOwlType(OWLClassExpression type) {
		OWLOntologyManager manager = this.owlOntology.getOWLOntologyManager();
		OWLDataFactory factory = manager.getOWLDataFactory();
		manager.addAxiom(this.owlOntology, factory.getOWLClassAssertionAxiom(type, this.owlIndividual));
	}

	/**
	 * Deletes the individual from Ontology
	 */
	public void delete() {
		OWLEntityRemover remover = new OWLEntityRemover(this.getOwlOntology().getOWLOntologyManager(), Collections.singleton(this.getOwlOntology()));
		this.owlIndividual.accept(remover);
		this.getOwlOntology().getOWLOntologyManager().applyChanges(remover.getChanges());
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof WrappedIndividual)) {
			return false;
		}
		WrappedIndividual other = (WrappedIndividual) obj;
		return other.getOwlOntology().equals(this.owlOntology) && other.getOwlIndividual().equals(this.owlIndividual);
	}

	@Override
	public int hashCode() {
		return this.owlOntology.hashCode() + 42 * this.owlIndividual.hashCode();
	}

	public int compareTo(WrappedIndividual o) {
		return this.owlIndividual.compareTo(o.getOwlIndividual());
	}

	@Override
	public String toString() {
		ShortFormProvider provider = new SimpleShortFormProvider();
		StringBuffer sb = new StringBuffer();
		this.printTypes(sb, provider);
		sb.append('(');
		this.printObjectPropertyValues(sb, provider);
		this.printDataPropertyValues(sb, provider);
		sb.append(')');
		return sb.toString();
	}

	private void printTypes(StringBuffer sb, ShortFormProvider provider) {
		Set<OWLClass> types = new TreeSet<OWLClass>();
		for (OWLClassExpression ce : this.owlIndividual.getTypes(this.owlOntology)) {
			if (!ce.isAnonymous()) {
				types.add(ce.asOWLClass());
			}
		}
		if (types.size() > 1) {
			sb.append('[');
		} else if (types.size() == 0) {
			sb.append("Untyped");
		}
		boolean firstTime = true;
		for (OWLClass type : types) {
			if (firstTime) {
				firstTime = false;
			} else {
				sb.append(", ");
			}
			sb.append(provider.getShortForm(type));
		}
		if (types.size() > 1) {
			sb.append(']');
		}
	}

	private void printObjectPropertyValues(StringBuffer sb, ShortFormProvider provider) {
		Map<OWLObjectPropertyExpression, Set<OWLIndividual>> valueMap = new TreeMap<OWLObjectPropertyExpression, Set<OWLIndividual>>(this.owlIndividual.getObjectPropertyValues(this.owlOntology));
		for (Entry<OWLObjectPropertyExpression, Set<OWLIndividual>> entry : valueMap.entrySet()) {
			OWLObjectPropertyExpression pe = entry.getKey();
			Set<OWLIndividual> values = entry.getValue();
			if (!pe.isAnonymous()) {
				OWLObjectProperty property = pe.asOWLObjectProperty();
				sb.append(provider.getShortForm(property));
				sb.append(": ");
				boolean firstTime = true;
				for (OWLIndividual value : values) {
					if (!value.isAnonymous()) {
						if (firstTime) {
							firstTime = false;
						} else {
							sb.append(", ");
						}
						sb.append(provider.getShortForm(value.asOWLNamedIndividual()));
					}
				}
				sb.append("; ");
			}
		}
	}

	private void printDataPropertyValues(StringBuffer sb, ShortFormProvider provider) {
		Map<OWLDataPropertyExpression, Set<OWLLiteral>> valueMap = new TreeMap<OWLDataPropertyExpression, Set<OWLLiteral>>(this.owlIndividual.getDataPropertyValues(this.owlOntology));
		for (Entry<OWLDataPropertyExpression, Set<OWLLiteral>> entry : valueMap.entrySet()) {
			OWLDataProperty property = entry.getKey().asOWLDataProperty();
			Set<OWLLiteral> values = entry.getValue();
			sb.append(provider.getShortForm(property));
			sb.append(": ");
			boolean firstTime = true;
			for (OWLLiteral value : values) {
				if (firstTime) {
					firstTime = false;
				} else {
					sb.append(", ");
				}
				sb.append(value.getLiteral());
			}
			sb.append("; ");
		}
	}

}

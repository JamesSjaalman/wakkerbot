/* $Id: python-interface.c,v 1.7 2004/01/13 10:59:20 lfousse Exp $ */
/* MegHAL Python interface, by David N. Welton <davidw@dedasys.com> */

#include <Python.h>
#include "megahal.h"

static PyObject *mhinitbrain(PyObject *self, PyObject *args)
{
    megahal_initialize();
	/* keep python's reference counting happy 
	http://code.activestate.com/recipes/52309-to-return-none-from-your-python-callable-c-functio/
	*/
    Py_INCREF(Py_None);

    return Py_None;
}

static PyObject *mhdoreply(PyObject *self, PyObject *args)
{
    char *input;
    char *output = NULL;

    if (!PyArg_ParseTuple(args, "s", &input))
	return NULL;
	/* Megahal's output consists of a malloced string, which is kept in a
	** 'static' pointer, Python presumably copies this string into it's own arena, and
	** handles the reference counting while doing so
	*/
    output = megahal_do_reply(input, 1);

    return PyString_FromString(output);
}

static PyObject *mhlearn(PyObject *self, PyObject *args)
{
    char *input;

    if (!PyArg_ParseTuple(args, "s", &input))
	return NULL;

    megahal_learn_no_reply(input, 1);

    Py_INCREF(Py_None);
    return Py_None;
}

static PyObject *mhdumptree(PyObject *self, PyObject *args)
{
    char *input;
    int flags=1;

    if (!PyArg_ParseTuple(args, "s|i", &input, &flags))
	return NULL;

    megahal_dumptree(input, flags);

    Py_INCREF(Py_None);
    return Py_None;
}

static PyObject *mhcleanup(PyObject *self, PyObject *args)
{
    megahal_cleanup();

    Py_INCREF(Py_None);
    return Py_None;
}

static struct PyMethodDef mh_methods[] = {
    {"initbrain", mhinitbrain, METH_VARARGS, "Initialize megahal brain"},
    {"doreply", mhdoreply, METH_VARARGS, "Generate a reply"},
    {"cleanup", mhcleanup, METH_VARARGS,"Clean megahal"},
    {"dumptree", mhdumptree, METH_VARARGS,"Dump Wakkerbot's brain to a file"},
    {"learn", mhlearn, METH_VARARGS, "Learn from a sentence, don't generate a reply"},
    {NULL, NULL, 0, NULL} /* Sentinel */
};

void initmh_python(void);
void initmh_python(void)
{
    Py_InitModule("mh_python", mh_methods);

    if(PyErr_Occurred())
	Py_FatalError("can't initialize module mh_python");
}

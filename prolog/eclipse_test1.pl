:- module(eclipse_test1,[]).

:- use_module(library(dict_atts)).

:- dicts_as_attvars(true).

:- meta_attribute(myattr, []).

:- meta_attribute(thing, [unify:unify_things/3, print_things/2]).

:- listing(meta_hook/3).

end_of_file.

:- export struct(dom(values,min,max)).
:- meta_attribute(dom, [
	unify:unify_doms/3,
	print:print_doms/2,
	suspension_lists:[
		min:[(min of dom)],
		max:[(max of dom)],
		both:[(min of dom),(max of dom)]
	    ]
    ]).




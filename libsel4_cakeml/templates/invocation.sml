{#
 # Copyright 2019, Data61
 # Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 # ABN 41 687 119 230.
 #
 # This software may be distributed and modified according to the terms of
 # the BSD 2-Clause license. Note that NO WARRANTY is provided.
 # See "LICENSE_BSD2.txt" for details.
 #
 # @TAG(DATA61_BSD)
 #}
(* {{name}}{% for param in all_params %} ({{param.name}}: {{param.type.name}}){% endfor %} *)
fun {{name}} {% if all_params == [] %}(){% else %}{{ all_params | map(attribute="name") | join(" ") }}{% endif %} = let
    {% if cap_params | length > 1 %}
    (* Cap params *)
    {% for cap in cap_params[1:] %}
    val u = SeL4.seL4_SetCap {{loop.index0}} {{cap.name}}
    {% endfor %}

    {% endif %}
    (* Input parameters passed in message registers *)
    {% for i in range(num_mrs) %}
    val mr{{i}} = {{input_expressions[i] or "Word64.fromInt 0"}}
    {% endfor %}

    {% if input_expressions | length > num_mrs %}
    (* Input parameters passed in the IPC buffer *)
    {% for i in range(num_mrs, input_expressions | length) %}
    val u = SeL4.seL4_SetMR ({{i}}) ({{input_expressions[i]}})
    {% endfor %}

    {% endif %}
    (* Make the system call *)
    (* {{method_id}} = {{method_id_num}} *)
    val tag = SeL4.seL4_MessageInfo_new {{method_id_num}} {{cap_params | length}} {{input_expressions | length}}
    {% if cakeml_v2_compatible %}
    (* Using CakeML 2 compatibility: no output parameters are supported! *)
    val err_code = SeL4.seL4_CallWithMRs {{cap_params[0].name}} tag{% for i in range(num_mrs) %} mr{{i}}{% endfor %}
    in
        err_code <> 0
    {% else %}
    (* NOTE: this code is bit-rotted *)
    val (error_code,
         {% for i in range(num_mrs) %}
         mr{{i}}{% if not loop.last %},
         {% endif %}
         {% endfor %}) = SeL4.seL4_CallWithMRs {{cap_params[0].name}} tag{% for i in range(num_mrs) %} mr{{i}}{% endfor %}

    {% if output_expressions | length > 0 %}
    (* Output parameters *)
    {% for (param, expr) in output_expressions %}
    val {{param.name}} = {{expr}}
    {% endfor %}
    {% endif %}
    in
        ({{ return_params | map(attribute="name") | join(", ") }})
    {% endif %}
    end



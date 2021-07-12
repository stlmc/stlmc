set verbose_level "0"
set on_failure_script_quits "1"
hycomp_read_model
hycomp_compile_model
hycomp_untime_network -m timed -n -d
hycomp_async2sync_network 
hycomp_net2mono

hycomp_check_invar_bmc -k 300 -a -P safe
time
quit
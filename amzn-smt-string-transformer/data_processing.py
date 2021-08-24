import pandas as pd
import numpy as np
import os 
import sys
import matplotlib
import matplotlib.pylab as plt
import json

TIMEOUT = 3600 # timeout in seconds

# for each query, get the SAT results of the original file, the transformed file,
# and the recon_check
# if there is nothing there, assume timeout
# first line of the file is the result
def get_SAT_results(query_name):
	# original results file: query_name.out
	original_result = get_result_from_file(query_name + ".out")
	# transformed results file: query_name_transformed.out
	transformed_result = get_result_from_file(query_name + "_transformed.out")
	# recon_check results file: query_name_recon_check.out
	recon_check_result = get_result_from_file(query_name + "_recon_check.out")

	return(pd.Series([original_result, transformed_result, recon_check_result]))


# plot a scatterplot of 2 sets of values. can choose to show the means
# and/or logscale the plots
# example: 
# scatterplot_vals_per_test((rel_results.trans_solver_time, "transformed"), (rel_results.orig_solver_time, "original"), 
# 								ylabel="Z3 runtime", yunits="(s)", logscale=True, showmeans=True)
def scatterplot_vals_per_test(list1, list2, yunits="", ylabel="", showmeans=False, logscale=False):
	(values_list1, label1) = list1
	(values_list2, label2) = list2
	xs = range(0, len(values_list1))
	plt.scatter(xs, values_list1, facecolors='none', edgecolors='r', label=label1, alpha=0.2 if showmeans else 1)
	plt.scatter(xs, values_list2, facecolors='none', edgecolors='b', label=label2, marker='^', alpha=0.2 if showmeans else 1)
	# plt.plot(xs, [TIMEOUT]*len(xs), label="Upperbound timeout")
	if showmeans:
		plt.axhline(y = values_list1.mean(), label=("Mean " + label1), linewidth = 3, color='r', linestyle='--')
		plt.axhline(y = values_list2.mean(), label=("Mean " + label2), linewidth = 3, color='b', linestyle=':')
	if logscale:
		plt.yscale('log')
	plt.xlabel("SMT query (index)")
	plt.ylabel(ylabel + " " + yunits)
	plt.title(ylabel + " for original and transformed queries")
	plt.legend()
	plt.show()

# same as previous function (for scatterplotting 2 lists), but this is just for one set of data
def scatterplot_one_list(list1, yunits="", ylabel="", showmeans=False, logscale=False):
	(values_list1, label1) = list1
	xs = range(0, len(values_list1))
	plt.scatter(xs, values_list1, facecolors='none', edgecolors='r', label=label1, marker='.', alpha=0.2 if showmeans else 1)
	if showmeans:
		plt.axhline(y = values_list1.mean(), label=("Mean " + label1), linewidth = 3, color='r', linestyle='--')
	if logscale:
		plt.yscale('log')
	plt.xlabel("SMT query (index)")
	plt.ylabel(ylabel + " " + yunits)
	plt.title(ylabel + " for all queries")
	plt.legend()
	plt.show()

# get a general stats summary of an input dataframe
# example:
# get_summary_table(rel_results)
def get_summary_table(df):
	count_disp = pd.DataFrame()
	count_disp["no_check_sat"] = [len(df[(df.orig_res == "no_check_sat")])]
	count_disp["all_gnup_timeout"] = [len(df[(df.orig_res == "gnu_timeout") & (df.trans_res == "gnu_timeout")])]
	count_disp["trans_only_gnup_timeout"] = [len(df[(df.orig_res != "gnu_timeout") & (df.trans_res == "gnu_timeout")])]
	count_disp["both_unsat"] = [len(df[(df.orig_res == "unsat") & (df.trans_res == "unsat")])]
	count_disp["both_sat"] = [len(df[(df.orig_res == "sat") & ((df.trans_res == "sat") | (df.trans_res == "sat: no model"))])]
	count_disp["sat_no_model"] = [len(df[df.trans_res == "sat: no model"])]
	count_disp["both_timeout"] = [len(df[(df.orig_res == "timeout") & (df.trans_res == "timeout")])]
	count_disp["orig_only_timeout"] = [len(df[(df.orig_res == "timeout") & (df.trans_res != "timeout")])]
	count_disp["trans_only_timeout"] = [len(df[(df.orig_res != "timeout") & (df.trans_res == "timeout")])]
	count_disp["orig_sat_trans_unsat"] = [len(df[(df.orig_res == "sat") & (df.trans_res == "unsat")])]
	count_disp["orig_unsat_trans_sat"] = [len(df[(df.orig_res == "unsat") & (df.trans_res == "sat")])]
	count_disp = count_disp.transpose()
	count_disp.columns = ["count"]

	time_disp = pd.DataFrame()
	# note: we don't need to dropna since these are ignored when computing means
	time_disp["orig_avg_time"] = [df.orig_solver_time.mean()]
	time_disp["orig_stdev_time"] = [df.orig_solver_time.std()]
	time_disp["trans_avg_time"] = [df.trans_solver_time.mean()]
	time_disp["trans_stdev_time"] = [df.trans_solver_time.std()]
	time_disp["convert_avg_time"] = [df.convert_time.mean()]
	time_disp["convert_stdev_time"] = [df.convert_time.std()]
	time_disp = time_disp.transpose()
	time_disp.columns = ["time (s)"]

	size_disp = pd.DataFrame()
	size_disp["orig_avg_size"] = [df.orig_size.mean()]
	size_disp["orig_stdev_size"] = [df.orig_size.std()]
	size_disp["trans_avg_size"] = [df.trans_size.mean()]
	size_disp["trans_stdev_size"] = [df.trans_size.std()]
	size_disp["map_avg_size"] = [df.map_size.mean()]
	size_disp["map_stdev_size"] = [df.map_size.std()]
	size_disp = size_disp.transpose()
	size_disp.columns = ["size (bytes)"]

	return((count_disp, time_disp, size_disp))


# get the number of seconds in a string from a linux time command result
def get_seconds( s):
	mins = float(s.split("m")[0])
	secs = float(s.split("m")[1].split("s")[0])
	return( mins*60 + secs)

# get the timing for the sequence of events timed by the test_and_transform.sh script
def get_timings(query_name):
	timings_filename = query_name + "_times.out"
	orig_solver = None 
	convert = None 
	trans_solver = None 
	reconstruct = None 
	recon_solver = None
	if os.path.isfile(timings_filename):
		with open(timings_filename) as f:
			orig_solver = get_timing_for_mode(query_name + ".smtlib", f)
			convert = get_timing_for_mode(query_name, f)
			trans_solver = get_timing_for_mode(query_name + "_transformed.smtlib", f)
	return(pd.Series([orig_solver, convert, trans_solver]))

# return NaN if file does not exist
def get_size(filename):
	try:
		return os.path.getsize(filename)
	except:
		return np.nan

def get_filesizes(query_name):
	orig_size = get_size(query_name + ".smtlib")
	trans_size = get_size(query_name + "_transformed.smtlib")
	map_size = get_size(query_name + "_mapping.json")
	return(pd.Series([orig_size, trans_size, map_size]))

def get_map_info(query_name):
	map_file = query_name + "_mapping.json"
	map_json = {}
	try:
		with open(map_file) as mf:
			map_json = json.load(mf)
	except:
		map_json = {}
	num_char_to_char_lits = len(map_json.get("char_to_char_string_lits", []))
	return(pd.Series(num_char_to_char_lits))

# we're getting the "user" time
# the format is: 
# command
# <empty line>
# real time
# user time
# sys time
def get_timing_for_mode(command, file_reader):
	try:
		cur_line = file_reader.readline()
		if cur_line.split("/")[-1].strip() != command:
			return(None)
		file_reader.readline() # empty line
		file_reader.readline() # real time
		cur_line = file_reader.readline().split("user\t")[-1]
		timing = get_seconds(cur_line)
		file_reader.readline() # sys time
		return(timing)
	except: 
		return(None)


# parse solver output to find result
def get_result_from_file(filename):
	result = "not_run"
	if os.path.isfile(filename):
		with open(filename) as f:
			firstline = f.readline().split("\n")[0]
			if len(firstline) > 0:
				if firstline.startswith("(error"):
					result = "error"
				elif firstline == "\"\"":
					result = "gnu_timeout"
				else:
					result = firstline
			else:
				result = "no_check_sat"
	return(result.lower())

# print dataframe to file
def printDFToFile( df, filename, print_index=False):
	f = open(filename, 'w');
	f.write(df.to_csv(index = print_index))
	f.close()

if len( sys.argv) < 2:
	print("Usage: python3 data_processing.py data_dir [optional: file with list of queries]")
else:
	data_dir = sys.argv[1]
	curdir = os.getcwd()
	all_queries = []
	if len(sys.argv) > 2:
		query_file_list = sys.argv[2]
		try:
			with open(query_file_list) as f:
				all_queries = [fname.split(".")[0] for fname in f.read().split("\n")]
		except:
			all_queries = []
	os.chdir(data_dir)
	if len(all_queries) == 0:
		all_queries = [f.split(".out")[0] for f in os.listdir() if f.find("in.out") > -1]
	ret_frame = pd.DataFrame(all_queries, columns=["query"])
	ret_frame[["orig_res", "trans_res", "recon_res"]] = ret_frame["query"].apply(get_SAT_results)
	ret_frame[["orig_solver_time", "convert_time", "trans_solver_time"]] = ret_frame["query"].apply(get_timings)
	ret_frame[["orig_size", "trans_size", "map_size"]] = ret_frame["query"].apply(get_filesizes)
	ret_frame["num_char_to_char_lits"] = ret_frame["query"].apply(get_map_info)

	# there is a difference between files empty because of no check-sat, and files empty because of timeouts
	# so, if the time is NaN, change the result to "gnu_timeout"
	ret_frame.orig_res = ret_frame.apply(lambda row: row.orig_res if not np.isnan(row.orig_solver_time) else "gnu_timeout", axis=1) 
	ret_frame.trans_res = ret_frame.apply(lambda row: row.trans_res if not np.isnan(row.trans_solver_time) else "gnu_timeout", axis=1)
	
	print(ret_frame)

	# useful commands if running in interactive mode
	rel_results = ret_frame[ret_frame.orig_res != "not_run"]
	# replace the NaN timings with the timeout value (NOTE: this is a design choice, we could also ignore these rows)
	rel_results.orig_solver_time = rel_results.orig_solver_time.fillna(TIMEOUT)
	rel_results.trans_solver_time = rel_results.trans_solver_time.fillna(TIMEOUT)

	
	# print(ret_frame)
	# printDFToFile( ret_frame, project_name + "_processed_data.csv")
	os.chdir(curdir)





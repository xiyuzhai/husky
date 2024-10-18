import numpy as np
import tiktoken
from tqdm import tqdm

FUNC_NAMES = [
    "calculate", "process", "handle", "display", "print_message", "read_file",
    "write_file", "parse_data", "serialize", "deserialize", "validate", "authenticate",
    "authorize", "hash_password", "encrypt", "decrypt", "send_email", "log_error",
    "log_info", "connect_database", "disconnect_database", "execute_query", "fetch_data",
    "update_record", "delete_record", "insert_record", "find_by_id", "search", "filter_data",
    "sort", "merge", "split", "join", "trim", "format_date", "get_current_time", "sleep",
    "restart_service", "shutdown", "upload_file", "download_file", "zip_files", "unzip_files",
    "parse_url", "encode_url", "decode_url", "send_request", "receive_response", "redirect",
    "render_template", "parse_json", "generate_json", "read_csv", "write_csv", "parse_xml",
    "generate_xml", "create_directory", "delete_directory", "list_directory", "copy_file",
    "move_file", "rename_file", "change_file_permissions", "change_directory", "get_file_size",
    "calculate_hash", "generate_uuid", "parse_arguments", "print_help", "set_configuration",
    "get_configuration", "save_configuration", "load_configuration", "initialize", "finalize",
    "start", "stop", "pause", "resume", "run", "execute", "call_api", "process_request",
    "process_response", "validate_request", "validate_response", "map_data", "reduce_data",
    "filter_list", "append_list", "remove_from_list", "insert_into_list", "pop_from_list",
    "clear_list", "index_of", "find_in_list", "sort_list", "reverse_list", "shuffle_list",
    "merge_lists", "split_list", "join_list", "slice_list", "chunk_list", "pair_list",
    "update_settings", "load_settings", "save_settings", "apply_settings", "configure",
    "setup", "teardown", "cleanup", "create_session", "destroy_session", "save_session",
    "load_session", "refresh", "reload", "parse_header", "format_header", "compress",
    "decompress", "encode", "decode", "hash", "sign", "verify_signature", "create_token",
    "validate_token", "revoke_token", "issue_token", "refresh_token", "generate_key",
    "validate_key", "encrypt_data", "decrypt_data", "serialize_object", "deserialize_object",
    "create_object", "destroy_object", "clone_object", "inspect_object", "monitor",
    "analyze", "diagnose", "repair", "optimize", "scale", "upgrade", "update", "patch",
    "backup", "restore", "import_data", "export_data", "sync_data", "merge_data", "split_data",
    "transform_data", "encode_data", "decode_data", "scan", "query", "build", "compile",
    "deploy", "publish", "retract", "log_debug", "log_warning", "assert_condition", "test_connection",
    "generate_report", "print_report", "create_report", "delete_report", "update_report",
    "send_notification", "schedule", "unschedule", "initiate_transfer", "complete_transfer",
    "abort_transfer", "calculate_difference", "compare", "diff", "merge_diff", "patch_diff",
    "validate_schema", "migrate", "seed_database", "clear_cache", "populate_cache", "invalidate_cache",
    "encrypt_file", "decrypt_file", "archive", "unarchive", "generate_checksum", "verify_checksum",
    "create_pipeline", "execute_pipeline", "terminate_pipeline", "schedule_job", "cancel_job",
    "retry_job", "execute_task", "complete_task", "abort_task", "allocate_resources", "release_resources"
]
VAR_NAMES = [
    'i', 'j', 'k', 'x', 'y', 'z', 'n', 'm', 't', 'val', 'value',
    'num', 'number', 'data', 'result', 'results', 'item', 'items',
    'elem', 'element', 'elements', 'list', 'lst', 'array', 'arr',
    'string', 'str', 'char', 'word', 'text', 'line', 'lines',
    'name', 'names', 'firstname', 'lastname', 'email', 'username',
    'password', 'url', 'path', 'dir', 'file', 'filename', 'filepath',
    'count', 'total', 'sum', 'avg', 'average', 'min', 'max',
    'length', 'len', 'size', 'index', 'pos', 'position', 'start',
    'end', 'status', 'state', 'flag', 'error', 'msg', 'message',
    'title', 'body', 'content', 'description', 'type', 'kind',
    'id', 'key', 'keys', 'value', 'values', 'data', 'payload',
    'json', 'xml', 'html', 'tag', 'tags', 'category', 'categories',
    'group', 'groups', 'batch', 'record', 'records', 'field', 'fields',
    'object', 'obj', 'instance', 'model', 'dict', 'dictionary', 'map',
    'mapping', 'table', 'queue', 'stack', 'tree', 'node', 'leaf',
    'branch', 'root', 'edge', 'vertex', 'vertices', 'graph',
    'function', 'func', 'method', 'algorithm', 'procedure',
    'action', 'activity', 'task', 'job', 'process', 'thread',
    'command', 'request', 'response', 'reply', 'output', 'input',
    'config', 'configuration', 'setting', 'settings', 'option',
    'options', 'param', 'parameter', 'parameters', 'arg', 'args',
    'argument', 'arguments', 'env', 'environment', 'version',
    'date', 'time', 'timestamp', 'year', 'month', 'day', 'hour',
    'minute', 'second', 'millisecond', 'timezone', 'period', 'duration',
    'interval', 'frequency', 'rate', 'ratio', 'percentage', 'percent',
    'score', 'point', 'points', 'grade', 'rating', 'rank',
    'level', 'stage', 'phase', 'cycle', 'sequence', 'list',
    'series', 'array', 'collection', 'bundle', 'packet', 'set',
    'batch', 'bundle', 'heap', 'pile', 'stack', 'queue', 'deque',
    'link', 'connection', 'channel', 'socket', 'port', 'protocol',
    'format', 'pattern', 'template', 'schema', 'outline', 'framework',
    'structure', 'system', 'platform', 'engine', 'tool', 'utility',
    'application', 'app', 'software', 'package', 'library', 'module',
    'script', 'code', 'program', 'project', 'repository', 'repo',
    'branch', 'version', 'release', 'patch', 'update', 'upgrade',
    'fix', 'bug', 'issue', 'error', 'warning', 'notice', 'alert',
    'log', 'report', 'history', 'record', 'comment', 'note', 'annotation'
]

INT_LITERALS = [str(i) for i in range(99)]
FLOAT_LITERALS = [f"{i}.1" for i in range(99)]
BOOL_LITERALS = ["true", "false"]

tokenizer = tiktoken.encoding_for_model("gpt2")

class AstKind:
    FnEntityName, ParameterType, ParameterIdent, FnEntityUsage, CallLpar, FnKeyword, LetKeyword, CallRpar, IntLiteral, FloatLiteral, BoolLiteral, ParametersLpar, ParametersRpar, FnBodyLcurl, FnBodyRcurl, ParameterTypeColon, StmtColon, FnArgComma = range(1, 19)

class SymbolResolution:
    Fn, Unresolved = 1, 2

class TypeError:
    Expected = 1

class Type:
    Bool, Int, Float = 1, 2, 3

    @classmethod
    def repr(cls, value):
        if value == cls.Bool:
            return "Bool"
        elif value == cls.Int:
            return "Int"
        elif value == cls.Float:
            return "Float"

class Function:
    def __init__(self, name, input_tys, last_called_step):
        self.name = name
        self.input_tys = input_tys
        self.last_called_step = last_called_step

class BasicCodeGenerator:
    def __init__(self, is_train, seed, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate):
        if is_train:
            self.func_names = FUNC_NAMES[:len(FUNC_NAMES) // 2]
            self.var_names = VAR_NAMES[:len(VAR_NAMES) // 2]
        else:
            self.func_names = FUNC_NAMES[len(FUNC_NAMES) // 2:]
            self.var_names = VAR_NAMES[len(VAR_NAMES) // 2:]

        self.rng = np.random.default_rng(seed)
        self.min_dist = min_dist
        self.use_var_rate = use_var_rate
        self.error_rate = error_rate
        self.max_args_per_fn = max_args_per_fn
        self.max_calls_per_fn = max_calls_per_fn
        self.used_fn_idx = []
        self.functions = []
        self.result = {
            "text": "",
            "token": [],
            "ast_kind": [],
            "symbol_resolution": [],
            "expected_type": [],
            "actual_type": []
        }
        self.time_step = 0

    def push_token(self, token, ast_kind=0, symbol_resolution=0, expected_type=0, actual_type=0):
        if self.result["text"]:
            self.result["text"] += " "
        self.result["text"] += token
        tokens = tokenizer.encode(token)
        for t in tokens:
            self.result["token"].append(t)
            self.result["ast_kind"].append(ast_kind)
            self.result["symbol_resolution"].append(symbol_resolution)
            self.result["expected_type"].append(expected_type)
            self.result["actual_type"].append(actual_type)

    def with_curly(self, lcurl_kind, rcurl_kind, f):
        self.push_token("{", lcurl_kind)
        f(self)
        self.push_token("}", rcurl_kind)

    def gen_fn(self, i):
        fn_name = self.chosen_fn_names[i]

        num_vars = self.rng.integers(low=1, high=self.max_args_per_fn + 1)
        input_tys = self.rng.choice([Type.Bool, Type.Int, Type.Float], num_vars).tolist()
        var_names = self.rng.choice(self.var_names, num_vars).tolist()

        self.push_token("fn", AstKind.FnKeyword)
        self.push_token(fn_name, AstKind.FnEntityName, SymbolResolution.Fn)
        self.push_token("(", AstKind.ParametersLpar)
        for i in range(num_vars):
            if i > 0:
                self.push_token(",", AstKind.FnArgComma)
            self.push_token(var_names[i], AstKind.ParameterIdent, expected_type=input_tys[i], actual_type=input_tys[i])
            self.push_token(":", AstKind.ParameterTypeColon)
            self.push_token(Type.repr(input_tys[i]), AstKind.ParameterType, expected_type=input_tys[i], actual_type=input_tys[i])

        self.push_token(")", AstKind.ParametersRpar)
        self.with_curly(AstKind.FnBodyLcurl, AstKind.FnBodyRcurl, lambda gen: self.gen_fn_body(var_names, input_tys))
        self.functions.append(Function(fn_name, input_tys, self.time_step))
        self.time_step += 1

    def gen_fn_body(self, var_names, input_tys):
        for _ in range(self.max_calls_per_fn):
            self.gen_fn_call(var_names, input_tys)

    def gen_fn_call(self, var_names, var_types):
        if not self.functions:
            return
        callee_index = self.rng.integers(low=0, high=len(self.functions))
        callee = self.functions[callee_index]

        if self.time_step - callee.last_called_step < self.min_dist:
            return
        callee.last_called_step = self.time_step

        fn_name = callee.name
        expected_types = callee.input_tys

        self.push_token(fn_name, AstKind.FnEntityUsage, SymbolResolution.Fn)
        self.push_token("(", AstKind.CallLpar)

        for i in range(len(expected_types)):
            if i > 0:
                self.push_token(",", AstKind.FnArgComma)

            use_var = self.rng.random() < self.use_var_rate
            if use_var:
                idx = self.rng.integers(low=0, high=len(var_names))
                arg_literal = var_names[idx]
                literal_kind = AstKind.ParameterIdent
                value_type = var_types[idx]
            else:
                has_ty_error = self.rng.random() < self.error_rate
                if has_ty_error:
                    types = [Type.Bool, Type.Int, Type.Float]
                    types.remove(expected_types[i])
                    value_type = self.rng.choice(types).item()
                else:
                    value_type = expected_types[i]
                arg_literal, literal_kind = self.get_literal_by_type(value_type)
            
            self.push_token(arg_literal, literal_kind, expected_type=expected_types[i], actual_type=value_type)

        self.push_token(")", AstKind.CallRpar)
        self.push_token(";", AstKind.StmtColon)

    def get_literal_by_type(self, value_type):
        if value_type == Type.Bool:
            return self.rng.choice(BOOL_LITERALS).item(), AstKind.BoolLiteral
        elif value_type == Type.Int:
            return self.rng.choice(INT_LITERALS).item(), AstKind.IntLiteral
        elif value_type == Type.Float:
            return self.rng.choice(FLOAT_LITERALS).item(), AstKind.FloatLiteral

    def gen_fns(self, max_fns):
        num_fns = self.rng.integers(low=max_fns // 2, high=max_fns + 1)
        self.chosen_fn_names = self.rng.choice(self.func_names, num_fns, replace=False)
        for i in range(num_fns):
            self.gen_fn(i)

    def finish(self):
        return self.result

from concurrent.futures import ProcessPoolExecutor
from tqdm import tqdm

def generate_code(is_train, seed, max_fns, max_args_per_fn, max_calls_per_fn,min_dist, use_var_rate, error_rate):
    """
    This function is a wrapper for the code generation process,
    designed to be called by each worker in the pool.
    """
    bcg = BasicCodeGenerator(is_train, seed, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate)
    bcg.gen_fns(max_fns)
    return bcg.finish()

def rnd_codes_parallel(is_train, n, max_fns, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate, workers=16):
    # Tuple of arguments to pass to each parallel invocation
    args = [(is_train, seed, max_fns, max_args_per_fn, max_calls_per_fn, min_dist, use_var_rate, error_rate) for seed in range(n)]
    
    # Use ProcessPoolExecutor to execute calls asynchronously
    with ProcessPoolExecutor(max_workers=workers) as executor:
        # Map the generate_code function to the arguments asynchronously
        # tqdm can be integrated with map() to show progress
        results = list(tqdm(executor.map(generate_code, *zip(*args), chunksize=1024), total=n))
    
    return results

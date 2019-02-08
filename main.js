#!/usr/bin/env node

var fs = require("fs");
var path = require("path");
var escoc = require("./escoc.js");

try {
  var args = [].slice.call(process.argv, 2);
  var file = args[args.length - 1] || "./main.escoc";
  var code = fs.readFileSync("./" + (file.indexOf(".") === -1 ? file + ".escoc" : file), "utf8");
} catch (e) {
  console.log("ESCoC: a nano proof language.");
  console.log("Usage: escoc file_name[.escoc]");
  process.exit();
}

var defs = escoc.parse(code);
var term = defs.main.term;

console.log("Term:\n" + escoc.show(term) + "\n");

try {
  console.log("Norm (head):\n" + escoc.show(escoc.norm(escoc.norm(term, defs, false), {}, true)) + "\n");
} catch (e) {
  console.log("Norm (head):\n<none?>\n");
}

try {
  console.log("Norm (full):\n" + escoc.show(escoc.norm(term, defs, true)) + "\n");
} catch (e) {
  console.log("Norm (full):\n<infinite?>\n");
}

try {
  var type = escoc.infer(term, defs);
  console.log("Type:\n" + escoc.show(type));
} catch (e) {
  console.log("Type:");
  console.log(e);
}

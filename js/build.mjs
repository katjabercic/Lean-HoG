import * as esbuild from 'esbuild'

async function buildFile(file) {
  await esbuild.build({
    entryPoints: [`src/${file}.jsx`],
    bundle: true,
    format: 'esm',
    minify: false,
    outfile: `../build/js/${file}.js`,
    external: ["react", "react-dom", "@leanprover/infoview"],
    banner: {
      js: 'const global = window;',
      css: ''
    }
  })
}

let files = ['app', 'helloWidget']

for (const file of files) {
  buildFile(file)
}
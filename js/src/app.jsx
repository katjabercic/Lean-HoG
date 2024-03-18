import React from "react";
import { createRoot } from 'react-dom/client';

function App() {
  return (
    <div>Hello, esbuild! </div>
  );
}
const container = document.getElementById('app');
const root = createRoot(container); // createRoot(container!) if you use TypeScript
root.render(<App tab="home" />);
# Why does salt make ice colder? — Vite project

This is the interactive simulation exported as a standalone Vite + React project.

## Setup

```bash
npm install
npm run dev
```

Then open the URL Vite prints (usually http://localhost:5173).

To build for production:

```bash
npm run build
npm run preview
```

## Structure

- `index.html` — Vite entry HTML (loads `src/main.jsx` as a module).
- `src/main.jsx` — React root bootstrap.
- `src/App.jsx` — the simulation: physics model, SVG drawing, and all React components.
- `src/styles.css` — all styling for the app.

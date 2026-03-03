language: node_js
node_js:
  - "0.10"
script:
  - "npm run test-travis"
after_script:
  - "npm install coveralls@2 && cat ./coverage/lcov.info | ./node_modules/.bin/coveralls"

xquery version "1.0-ml";

module namespace {{MODULE_PREFIX}} = "http://marklogic.com/rest-api/resource/{{ENDPOINT_NAME}}";

import module namespace rh = "https://pubs.cas.org/modules/lib/rest-helper" at "/lib/rest-helper.xqy";
import module namespace const = "https://pubs.cas.org/modules/lib/constants" at "/lib/constants.xqy";
import module namespace log = "https://pubs.cas.org/modules/lib/logger" at "/lib/logger.xqy";

(:~
 : GET endpoint handler
 : @param $context - MarkLogic REST API context map
 : @param $params - Query parameters from the request
 : @return Document node with response
 :)
declare function {{MODULE_PREFIX}}:get(
    $context as map:map,
    $params as map:map
) as document-node()* {

    (: Extract parameters :)
    let $param1 := map:get($params, "param1")

    (: Define validation rules :)
    let $rules := (
        map:new()
            => map:with("value", $param1)
            => map:with("validation-function", "not-empty")
            => map:with("response-code", $const:HTTP_BAD_REQUEST)
            => map:with("response-message", "param1 is required")
    )

    (: Validate request :)
    let $validation-result := rh:validate($rules)

    return (
        if (not(empty($validation-result))) then
            rh:set-output-status($context, $validation-result)
        else
            (: TODO: Implement business logic here :)
            xdmp:to-json(map:new()
                => map:with("result", "success")
                => map:with("data", ())
            )
        , log:trace("{{ENDPOINT_NAME_UPPER}}_ENDPOINT", $params)
    )
};

(:~
 : POST endpoint handler
 : @param $context - MarkLogic REST API context map
 : @param $params - Query parameters from the request
 : @param $input - Request body as document node
 : @return Document node with response
 :)
declare function {{MODULE_PREFIX}}:post(
    $context as map:map,
    $params as map:map,
    $input as document-node()*
) as document-node()? {

    (: Parse JSON input :)
    let $json-obj := rh:objectify-post-input($input)

    (: Extract parameters from request body :)
    let $field1 := $json-obj/field1/string()

    (: Define validation rules :)
    let $rules := (
        map:new()
            => map:with("value", $field1)
            => map:with("validation-function", "not-empty")
            => map:with("response-code", $const:HTTP_BAD_REQUEST)
            => map:with("response-message", "field1 is required")
    )

    (: Validate request :)
    let $validation-result := rh:validate($rules)

    return (
        if (not(empty($validation-result))) then
            rh:set-output-status($context, $validation-result)
        else
            (: TODO: Implement business logic here :)
            xdmp:to-json(map:new()
                => map:with("result", "success")
                => map:with("data", ())
            )
        , log:trace("{{ENDPOINT_NAME_UPPER}}_ENDPOINT", $input)
    )
};

(:~
 : PUT endpoint handler (optional)
 : Throws error if not supported
 :)
declare function {{MODULE_PREFIX}}:put(
    $context as map:map,
    $params as map:map,
    $input as document-node()*
) as document-node()? {
    fn:error(xs:QName("UNSUPPORTED-HTTP-METHOD"), "PUT method is not supported for this endpoint")
};

(:~
 : DELETE endpoint handler (optional)
 : Throws error if not supported
 :)
declare function {{MODULE_PREFIX}}:delete(
    $context as map:map,
    $params as map:map
) as document-node()? {
    fn:error(xs:QName("UNSUPPORTED-HTTP-METHOD"), "DELETE method is not supported for this endpoint")
};

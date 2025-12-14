# WordPress Database Operations

## $wpdb Global Object

```php
global $wpdb;

// Table names (with prefix)
$wpdb->posts;           // wp_posts
$wpdb->postmeta;        // wp_postmeta
$wpdb->users;           // wp_users
$wpdb->usermeta;        // wp_usermeta
$wpdb->options;         // wp_options
$wpdb->terms;           // wp_terms
$wpdb->term_taxonomy;   // wp_term_taxonomy
$wpdb->term_relationships; // wp_term_relationships
$wpdb->comments;        // wp_comments
$wpdb->commentmeta;     // wp_commentmeta
$wpdb->prefix;          // 'wp_' (or custom prefix)
```

## Secure Query Methods

### Always Use prepare()

```php
// Single value
$result = $wpdb->get_var(
    $wpdb->prepare(
        "SELECT post_title FROM {$wpdb->posts} WHERE ID = %d",
        $post_id
    )
);

// Single row
$row = $wpdb->get_row(
    $wpdb->prepare(
        "SELECT * FROM {$wpdb->posts} WHERE ID = %d",
        $post_id
    )
);

// Multiple rows
$results = $wpdb->get_results(
    $wpdb->prepare(
        "SELECT * FROM {$wpdb->posts} WHERE post_author = %d AND post_status = %s",
        $author_id,
        'publish'
    )
);

// Single column
$ids = $wpdb->get_col(
    $wpdb->prepare(
        "SELECT ID FROM {$wpdb->posts} WHERE post_type = %s",
        'post'
    )
);
```

### Placeholders

- `%d` - integer
- `%f` - float
- `%s` - string
- `%i` - identifier (table/column names, WP 6.2+)

### Insert, Update, Delete

```php
// Insert
$wpdb->insert(
    $wpdb->prefix . 'custom_table',
    array(
        'column1' => $value1,
        'column2' => $value2,
    ),
    array( '%s', '%d' ) // Format for each value
);
$inserted_id = $wpdb->insert_id;

// Update
$wpdb->update(
    $wpdb->prefix . 'custom_table',
    array( 'column1' => $new_value ), // Data
    array( 'id' => $id ),              // Where
    array( '%s' ),                     // Data format
    array( '%d' )                      // Where format
);

// Delete
$wpdb->delete(
    $wpdb->prefix . 'custom_table',
    array( 'id' => $id ),
    array( '%d' )
);

// Replace (insert or update)
$wpdb->replace(
    $wpdb->prefix . 'custom_table',
    array(
        'id'      => $id,
        'column1' => $value,
    ),
    array( '%d', '%s' )
);
```

## Custom Tables

### Creating Tables

```php
register_activation_hook( __FILE__, 'my_prefix_create_table' );
function my_prefix_create_table() {
    global $wpdb;

    $table_name = $wpdb->prefix . 'custom_table';
    $charset_collate = $wpdb->get_charset_collate();

    $sql = "CREATE TABLE $table_name (
        id bigint(20) unsigned NOT NULL AUTO_INCREMENT,
        user_id bigint(20) unsigned NOT NULL,
        data longtext NOT NULL,
        status varchar(20) NOT NULL DEFAULT 'active',
        created_at datetime NOT NULL DEFAULT CURRENT_TIMESTAMP,
        updated_at datetime NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
        PRIMARY KEY  (id),
        KEY user_id (user_id),
        KEY status (status)
    ) $charset_collate;";

    require_once ABSPATH . 'wp-admin/includes/upgrade.php';
    dbDelta( $sql );

    add_option( 'my_prefix_db_version', '1.0' );
}
```

### dbDelta Requirements

- Each field on its own line
- Two spaces between PRIMARY KEY and opening parenthesis
- Use KEY instead of INDEX
- No apostrophes around field names

### Table Upgrades

```php
function my_prefix_update_db_check() {
    $installed_ver = get_option( 'my_prefix_db_version' );
    if ( $installed_ver !== '1.1' ) {
        my_prefix_upgrade_table();
    }
}
add_action( 'plugins_loaded', 'my_prefix_update_db_check' );

function my_prefix_upgrade_table() {
    global $wpdb;
    $table_name = $wpdb->prefix . 'custom_table';

    // Add new column
    $wpdb->query( "ALTER TABLE $table_name ADD COLUMN new_field varchar(255) DEFAULT NULL" );

    update_option( 'my_prefix_db_version', '1.1' );
}
```

## WP_Query vs Direct Queries

**Use WP_Query for posts:**

```php
$query = new WP_Query( array(
    'post_type'      => 'product',
    'posts_per_page' => 10,
    'meta_query'     => array(
        array(
            'key'     => '_price',
            'value'   => 100,
            'compare' => '>=',
            'type'    => 'NUMERIC',
        ),
    ),
) );
```

**Use $wpdb for:**
- Custom tables
- Complex joins
- Aggregate functions
- Performance-critical queries

## Transactions

```php
global $wpdb;

$wpdb->query( 'START TRANSACTION' );

try {
    $wpdb->insert( /* ... */ );
    $wpdb->update( /* ... */ );

    if ( $wpdb->last_error ) {
        throw new Exception( $wpdb->last_error );
    }

    $wpdb->query( 'COMMIT' );
} catch ( Exception $e ) {
    $wpdb->query( 'ROLLBACK' );
    error_log( 'Transaction failed: ' . $e->getMessage() );
}
```

## Error Handling

```php
// Suppress errors
$wpdb->suppress_errors();

// Check last error
if ( $wpdb->last_error ) {
    error_log( 'Database error: ' . $wpdb->last_error );
}

// Last query (for debugging)
error_log( 'Last query: ' . $wpdb->last_query );

// Rows affected
$rows = $wpdb->rows_affected;
```

## Performance Tips

```php
// Use specific columns instead of *
$wpdb->get_results( "SELECT id, title FROM ..." );

// Add LIMIT to prevent large result sets
$wpdb->get_results( $wpdb->prepare(
    "SELECT * FROM {$wpdb->posts} WHERE post_type = %s LIMIT %d",
    'post',
    100
) );

// Use indexes
// Create indexes on columns used in WHERE, JOIN, ORDER BY

// Cache results
$cache_key = 'my_query_' . md5( serialize( $args ) );
$results = wp_cache_get( $cache_key );
if ( false === $results ) {
    $results = $wpdb->get_results( /* ... */ );
    wp_cache_set( $cache_key, $results, '', 3600 );
}
```

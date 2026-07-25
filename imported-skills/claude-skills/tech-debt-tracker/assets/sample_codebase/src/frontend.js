// Frontend JavaScript with various technical debt examples

// TODO: Move configuration to separate file
const API_BASE_URL = "https://api.example.com";
const API_KEY = "abc123def456"; // FIXME: Should be in environment

// Global variables - should be encapsulated
var userCache = {};
var authToken = null;
var currentUser = null;

// HACK: Polyfill for older browsers - should use proper build system
if (!String.prototype.includes) {
    String.prototype.includes = function(search) {
        return this.indexOf(search) !== -1;
    };
}

class UserInterface {
    constructor() {
        this.components = {};
        this.eventHandlers = [];
        
        // Long parameter list in constructor
        this.init(document, window, localStorage, sessionStorage, navigator, history, location);
    }
    
    // Function with too many parameters
    init(doc, win, localStorage, sessionStorage, nav, hist, loc) {
        this.document = doc;
        this.window = win;
        this.localStorage = localStorage;
        this.sessionStorage = sessionStorage;
        this.navigator = nav;
        this.history = hist;
        this.location = loc;
        
        // Deep nesting example
        if (this.localStorage) {
            if (this.localStorage.getItem('user')) {
                if (JSON.parse(this.localStorage.getItem('user'))) {
                    if (JSON.parse(this.localStorage.getItem('user')).preferences) {
                        if (JSON.parse(this.localStorage.getItem('user')).preferences.theme) {
                            if (JSON.parse(this.localStorage.getItem('user')).preferences.theme === 'dark') {
                                document.body.classList.add('dark-theme');
                            } else if (JSON.parse(this.localStorage.getItem('user')).preferences.theme === 'light') {
                                document.body.classList.add('light-theme');
                            } else {
                                document.body.classList.add('default-theme');
                            }
                        }
                    }
                }
            }
        }
    }
    
    // Large function that does too many things
    renderUserDashboard(userId, includeStats, includeRecent, includeNotifications, includeSettings, includeHelp) {
        let user = this.getUser(userId);
        
        if (!user) {
            console.log("User not found"); // Should use proper logging
            return;
        }
        
        let html = '<div class="dashboard">';
        
        // Inline HTML generation - should use templates
        html += '<header class="dashboard-header">';
        html += '<h1>Welcome, ' + user.name + '</h1>';
        html += '<div class="user-avatar">';
        html += '<img src="' + user.avatar + '" alt="Avatar" />';
        html += '</div>';
        html += '</header>';
        
        // Repeated validation pattern
        if (includeStats && includeStats === true) {
            html += '<section class="stats">';
            html += '<h2>Your Statistics</h2>';
            
            // Magic numbers everywhere
            if (user.loginCount > 100) {
                html += '<div class="stat-item">Frequent User (100+ logins)</div>';
            } else if (user.loginCount > 50) {
                html += '<div class="stat-item">Regular User (50+ logins)</div>';
            } else if (user.loginCount > 10) {
                html += '<div class="stat-item">Casual User (10+ logins)</div>';
            } else {
                html += '<div class="stat-item">New User</div>';
            }
            
            html += '</section>';
        }
        
        if (includeRecent && includeRecent === true) {
            html += '<section class="recent">';
            html += '<h2>Recent Activity</h2>';
            
            // No error handling for API calls
            let recentActivity = this.fetchRecentActivity(userId);
            
            if (recentActivity && recentActivity.length > 0) {
                html += '<ul class="activity-list">';
                for (let i = 0; i < recentActivity.length; i++) {
                    let activity = recentActivity[i];
                    html += '<li class="activity-item">';
                    html += '<span class="activity-type">' + activity.type + '</span>';
                    html += '<span class="activity-description">' + activity.description + '</span>';
                    html += '<span class="activity-time">' + this.formatTime(activity.timestamp) + '</span>';
                    html += '</li>';
                }
                html += '</ul>';
            } else {
                html += '<p>No recent activity</p>';
            }
            
            html += '</section>';
        }
        
        if (includeNotifications && includeNotifications === true) {
            html += '<section class="notifications">';
            html += '<h2>Notifications</h2>';
            
            let notifications = this.getNotifications(userId);
            
            // Duplicate HTML generation pattern
            if (notifications && notifications.length > 0) {
                html += '<ul class="notification-list">';
                for (let i = 0; i < notifications.length; i++) {
                    let notification = notifications[i];
                    html += '<li class="notification-item">';
                    html += '<span class="notification-title">' + notification.title + '</span>';
                    html += '<span class="notification-message">' + notification.message + '</span>';
                    html += '<span class="notification-time">' + this.formatTime(notification.timestamp) + '</span>';
                    html += '</li>';
                }
                html += '</ul>';
            } else {
                html += '<p>No notifications</p>';
            }
            
            html += '</section>';
        }
        
        html += '</div>';
        
        // Direct DOM manipulation without cleanup
        document.getElementById('main-content').innerHTML = html;
        
        // Event handler attachment without cleanup
        let buttons = document.querySelectorAll('.action-button');
        for (let i = 0; i < buttons.length; i++) {
            buttons[i].addEventListener('click', function(event) {
                // Nested event handlers - memory leak risk
                let buttonType = event.target.getAttribute('data-type');
                if (buttonType === 'edit') {
                    // Inline event handling - should be separate methods
                    let modal = document.createElement('div');
                    modal.className = 'modal';
                    modal.innerHTML = '<div class="modal-content"><h3>Edit Profile</h3><button onclick="closeModal()">Close</button></div>';
                    document.body.appendChild(modal);
                } else if (buttonType === 'delete') {
                    if (confirm('Are you sure?')) {  // Using confirm - poor UX
                        // No error handling
                        fetch(API_BASE_URL + '/users/' + userId, {
                            method: 'DELETE',
                            headers: {'Authorization': 'Bearer ' + authToken}
                        });
                    }
                } else if (buttonType === 'share') {
                    // Hardcoded share logic
                    if (navigator.share) {
                        navigator.share({
                            title: 'Check out my profile',
                            url: window.location.href
                        });
                    } else {
                        // Fallback for browsers without Web Share API
                        let shareUrl = 'https://twitter.com/intent/tweet?url=' + encodeURIComponent(window.location.href);
                        window.open(shareUrl, '_blank');
                    }
                }
            });
        }
    }
    
    // Duplicate code - similar to above but for admin dashboard
    renderAdminDashboard(adminId) {
        let admin = this.getUser(adminId);
        
        if (!admin) {
            console.log("Admin not found");
            return;
        }
        
        let html = '<div class="admin-dashboard">';
        
        html += '<header class="dashboard-header">';
        html += '<h1>Admin Panel - Welcome, ' + admin.name + '</h1>';
        html += '<div class="user-avatar">';
        html += '<img src="' + admin.avatar + '" alt="Avatar" />';
        html += '</div>';
        html += '</header>';
        
        // Same pattern repeated
        html += '<section class="admin-stats">';
        html += '<h2>System Statistics</h2>';
        
        let stats = this.getSystemStats();
        if (stats) {
            html += '<div class="stat-grid">';
            html += '<div class="stat-item">Total Users: ' + stats.totalUsers + '</div>';
            html += '<div class="stat-item">Active Users: ' + stats.activeUsers + '</div>';
            html += '<div class="stat-item">New Today: ' + stats.newToday + '</div>';
            html += '</div>';
        }
        
        html += '</section>';
        html += '</div>';
        
        document.getElementById('main-content').innerHTML = html;
    }
    
    getUser(userId) {
        // Check cache first - but cache never expires
        if (userCache[userId]) {
            return userCache[userId];
        }
        
        // Synchronous AJAX - blocks UI
        let xhr = new XMLHttpRequest();
        xhr.open('GET', API_BASE_URL + '/users/' + userId, false);
        xhr.setRequestHeader('Authorization', 'Bearer ' + authToken);
        xhr.send();
        
        if (xhr.status === 200) {
            let user = JSON.parse(xhr.responseText);
            userCache[userId] = user;
            return user;
        } else {
            // Generic error handling
            console.error('Failed to fetch user');
            return null;
        }
    }
    
    fetchRecentActivity(userId) {
        // Another synchronous call
        try {
            let xhr = new XMLHttpRequest();
            xhr.open('GET', API_BASE_URL + '/users/' + userId + '/activity', false);
            xhr.setRequestHeader('Authorization', 'Bearer ' + authToken);
            xhr.send();
            
            if (xhr.status === 200) {
                return JSON.parse(xhr.responseText);
            } else {
                return [];
            }
        } catch (error) {
            // Swallowing errors
            return [];
        }
    }
    
    getNotifications(userId) {
        // Yet another sync call - should be async
        let xhr = new XMLHttpRequest();
        xhr.open('GET', API_BASE_URL + '/users/' + userId + '/notifications', false);
        xhr.setRequestHeader('Authorization', 'Bearer ' + authToken);
        xhr.send();
        
        if (xhr.status === 200) {
            return JSON.parse(xhr.responseText);
        } else {
            return [];
        }
    }
    
    formatTime(timestamp) {
        // Basic time formatting - should use proper library
        let date = new Date(timestamp);
        return date.getMonth() + '/' + date.getDate() + '/' + date.getFullYear();
    }
    
    // XXX: This method is never used
    formatCurrency(amount, currency) {
        if (currency === 'USD') {
            return '$' + amount.toFixed(2);
        } else if (currency === 'EUR') {
            return '€' + amount.toFixed(2);
        } else {
            return amount.toFixed(2) + ' ' + currency;
        }
    }
    
    getSystemStats() {
        // Hardcoded test data - should come from API
        return {
            totalUsers: 12534,
            activeUsers: 8765,
            newToday: 23
        };
    }
}

// Global functions - should be methods or modules
function closeModal() {
    // Assumes modal exists - no error checking
    document.querySelector('.modal').remove();
}

function validateEmail(email) {
    // Regex without explanation - magic pattern
    return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
}

function validatePassword(password) {
    // Duplicate validation logic from backend
    if (password.length < 8) return false;
    if (!/[A-Z]/.test(password)) return false;
    if (!/[a-z]/.test(password)) return false;
    if (!/\d/.test(password)) return false;
    return true;
}

// jQuery-style utility - reinventing the wheel
function $(selector) {
    return document.querySelector(selector);
}

function $all(selector) {
    return document.querySelectorAll(selector);
}

// Global event handlers - should be encapsulated
document.addEventListener('DOMContentLoaded', function() {
    // Inline anonymous function
    let ui = new UserInterface();
    
    // Event delegation would be better
    document.body.addEventListener('click', function(event) {
        if (event.target.classList.contains('login-button')) {
            // Inline login logic
            let username = $('#username').value;
            let password = $('#password').value;
            
            if (!username || !password) {
                alert('Please enter username and password'); // Poor UX
                return;
            }
            
            // No CSRF protection
            fetch(API_BASE_URL + '/auth/login', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({username: username, password: password})
            })
            .then(response => response.json())
            .then(data => {
                if (data.success) {
                    authToken = data.token;
                    currentUser = data.user;
                    localStorage.setItem('authToken', authToken); // Storing sensitive data
                    localStorage.setItem('currentUser', JSON.stringify(currentUser));
                    window.location.reload(); // Poor navigation
                } else {
                    alert('Login failed: ' + data.error);
                }
            })
            .catch(error => {
                console.error('Login error:', error);
                alert('Login failed');
            });
        }
    });
});

// // Old code left as comments - should be removed
// function oldRenderFunction() {
//     var html = '<div>Old implementation</div>';
//     document.body.innerHTML = html;
// }

// Commented out feature - should be removed or implemented
// function darkModeToggle() {
//     if (document.body.classList.contains('dark-theme')) {
//         document.body.classList.remove('dark-theme');
//         document.body.classList.add('light-theme');
//     } else {
//         document.body.classList.remove('light-theme');
//         document.body.classList.add('dark-theme');
//     }
// }
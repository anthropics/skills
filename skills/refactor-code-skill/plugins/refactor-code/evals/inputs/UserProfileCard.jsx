import React, { useState, useEffect } from 'react';

function UserProfileCard({ userId }) {
  const [user, setUser] = useState(null);
  const [posts, setPosts] = useState([]);
  const [isLoading, setIsLoading] = useState(true);
  const [isEditing, setIsEditing] = useState(false);
  const [editedName, setEditedName] = useState('');
  const [editedEmail, setEditedEmail] = useState('');
  const [error, setError] = useState(null);

  useEffect(() => {
    setIsLoading(true);
    fetch(`/api/users/${userId}`)
      .then(res => res.json())
      .then(data => {
        setUser(data);
        setEditedName(data.name);
        setEditedEmail(data.email);
      })
      .catch(err => setError(err.message))
      .finally(() => setIsLoading(false));
  }, [userId]);

  useEffect(() => {
    if (user) {
      fetch(`/api/users/${userId}/posts`)
        .then(res => res.json())
        .then(data => setPosts(data));
    }
  }, [user, userId]);

  function handleSave() {
    fetch(`/api/users/${userId}`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ name: editedName, email: editedEmail })
    })
      .then(res => res.json())
      .then(data => {
        setUser(data);
        setIsEditing(false);
      })
      .catch(err => setError(err.message));
  }

  if (isLoading) {
    return <div className="loading">Loading...</div>;
  }

  if (error) {
    return <div className="error">Error: {error}</div>;
  }

  if (!user) {
    return <div className="error">No user found</div>;
  }

  return (
    <div className="user-profile-card">
      {isEditing ? (
        <div>
          <input
            type="text"
            value={editedName}
            onChange={(e) => setEditedName(e.target.value)}
          />
          <input
            type="email"
            value={editedEmail}
            onChange={(e) => setEditedEmail(e.target.value)}
          />
          <button onClick={handleSave}>Save</button>
          <button onClick={() => setIsEditing(false)}>Cancel</button>
        </div>
      ) : (
        <div>
          <h2>{user.name}</h2>
          <p>{user.email}</p>
          <p>Joined: {new Date(user.joinedAt).toLocaleDateString()}</p>
          {user.isAdmin && <span className="badge">Admin</span>}
          {user.isPremium && <span className="badge">Premium</span>}
          <button onClick={() => setIsEditing(true)}>Edit</button>
        </div>
      )}

      <div className="posts-section">
        <h3>Recent Posts ({posts.length})</h3>
        {posts.length === 0 ? (
          <p>No posts yet</p>
        ) : (
          <ul>
            {posts.slice(0, 5).map(post => (
              <li key={post.id}>
                <a href={`/posts/${post.id}`}>{post.title}</a>
                <span className="date">
                  {new Date(post.createdAt).toLocaleDateString()}
                </span>
              </li>
            ))}
          </ul>
        )}
      </div>
    </div>
  );
}

export default UserProfileCard;

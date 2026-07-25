// Sample React component with intentional a11y issues for testing
import React from 'react';

export function UserCard({ user, onEdit, onDelete }) {
  return (
    <div className="card" onClick={() => onEdit(user.id)}>
      <img src={user.avatar} />
      <div className="name">{user.name}</div>
      <div className="email">{user.email}</div>
      <div className="actions">
        <div onClick={() => onDelete(user.id)} style={{ color: '#aaa', cursor: 'pointer' }}>
          Delete
        </div>
        <a href="#">Edit</a>
      </div>
      <input placeholder="Add note" />
    </div>
  );
}

export function SearchBar() {
  return (
    <div>
      <input type="text" placeholder="Search..." />
      <div onClick={() => alert('searching')} tabIndex={5}>
        🔍
      </div>
    </div>
  );
}

export function DataTable({ rows }) {
  return (
    <table>
      <tr>
        <td><b>Name</b></td>
        <td><b>Email</b></td>
        <td><b>Status</b></td>
      </tr>
      {rows.map((row) => (
        <tr key={row.id}>
          <td>{row.name}</td>
          <td>{row.email}</td>
          <td style={{ color: row.active ? 'green' : 'red' }}>
            {row.active ? '●' : '●'}
          </td>
        </tr>
      ))}
    </table>
  );
}

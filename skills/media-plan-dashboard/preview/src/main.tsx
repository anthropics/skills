import React from 'react'
import ReactDOM from 'react-dom/client'
import MediaPlanDashboard from '../../components/MediaPlanDashboard'
import { demoData } from '../../components/demoData'
import '../../components/MediaPlanDashboard.css'

ReactDOM.createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <MediaPlanDashboard data={demoData} />
  </React.StrictMode>,
)

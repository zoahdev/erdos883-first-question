import Erdos883AdaptiveSpan18801Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength18801_4 : adaptiveNumericSpans18801_4.length = 421 := by decide +kernel
theorem adaptiveSpanEvenCache18801_4 : adaptiveSpanEven18801_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain18801_4 : adaptiveSpanEven18801_4.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanEvenEntries18801_4 : adaptiveSpanEven18801_4.spans = coreEvenSpans 9401 0 adaptiveNumericSpans18801_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache18801_4 : adaptiveSpanWhole18801_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain18801_4 : adaptiveSpanWhole18801_4.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanWholeEntries18801_4 : adaptiveSpanWhole18801_4.spans = coreWholeSpans 0 adaptiveNumericSpans18801_4 := by
  decide +kernel
end Erdos883Verified

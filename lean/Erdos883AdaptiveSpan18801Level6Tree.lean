import Erdos883AdaptiveSpan18801Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength18801_6 : adaptiveNumericSpans18801_6.length = 421 := by decide +kernel
theorem adaptiveSpanEvenCache18801_6 : adaptiveSpanEven18801_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain18801_6 : adaptiveSpanEven18801_6.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanEvenEntries18801_6 : adaptiveSpanEven18801_6.spans = coreEvenSpans 9401 0 adaptiveNumericSpans18801_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache18801_6 : adaptiveSpanWhole18801_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain18801_6 : adaptiveSpanWhole18801_6.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanWholeEntries18801_6 : adaptiveSpanWhole18801_6.spans = coreWholeSpans 0 adaptiveNumericSpans18801_6 := by
  decide +kernel
end Erdos883Verified

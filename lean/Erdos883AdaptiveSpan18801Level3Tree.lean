import Erdos883AdaptiveSpan18801Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength18801_3 : adaptiveNumericSpans18801_3.length = 421 := by decide +kernel
theorem adaptiveSpanEvenCache18801_3 : adaptiveSpanEven18801_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain18801_3 : adaptiveSpanEven18801_3.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanEvenEntries18801_3 : adaptiveSpanEven18801_3.spans = coreEvenSpans 9401 0 adaptiveNumericSpans18801_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache18801_3 : adaptiveSpanWhole18801_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain18801_3 : adaptiveSpanWhole18801_3.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanWholeEntries18801_3 : adaptiveSpanWhole18801_3.spans = coreWholeSpans 0 adaptiveNumericSpans18801_3 := by
  decide +kernel
end Erdos883Verified

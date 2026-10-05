import Erdos883AdaptiveSpan18801Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength18801_1 : adaptiveNumericSpans18801_1.length = 421 := by decide +kernel
theorem adaptiveSpanEvenCache18801_1 : adaptiveSpanEven18801_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain18801_1 : adaptiveSpanEven18801_1.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanEvenEntries18801_1 : adaptiveSpanEven18801_1.spans = coreEvenSpans 9401 0 adaptiveNumericSpans18801_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache18801_1 : adaptiveSpanWhole18801_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain18801_1 : adaptiveSpanWhole18801_1.domainCheck 9401 = true := by decide +kernel
theorem adaptiveSpanWholeEntries18801_1 : adaptiveSpanWhole18801_1.spans = coreWholeSpans 0 adaptiveNumericSpans18801_1 := by
  decide +kernel
end Erdos883Verified

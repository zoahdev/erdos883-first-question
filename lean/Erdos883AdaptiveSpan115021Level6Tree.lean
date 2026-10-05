import Erdos883AdaptiveSpan115021Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_6 : adaptiveNumericSpans115021_6.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_6 : adaptiveSpanEven115021_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_6 : adaptiveSpanEven115021_6.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_6 : adaptiveSpanEven115021_6.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_6 : adaptiveSpanWhole115021_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_6 : adaptiveSpanWhole115021_6.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_6 : adaptiveSpanWhole115021_6.spans = coreWholeSpans 0 adaptiveNumericSpans115021_6 := by
  decide +kernel
end Erdos883Verified

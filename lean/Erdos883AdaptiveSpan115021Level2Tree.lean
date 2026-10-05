import Erdos883AdaptiveSpan115021Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_2 : adaptiveNumericSpans115021_2.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_2 : adaptiveSpanEven115021_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_2 : adaptiveSpanEven115021_2.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_2 : adaptiveSpanEven115021_2.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_2 : adaptiveSpanWhole115021_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_2 : adaptiveSpanWhole115021_2.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_2 : adaptiveSpanWhole115021_2.spans = coreWholeSpans 0 adaptiveNumericSpans115021_2 := by
  decide +kernel
end Erdos883Verified

import Erdos883AdaptiveSpan115021Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_8 : adaptiveNumericSpans115021_8.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_8 : adaptiveSpanEven115021_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_8 : adaptiveSpanEven115021_8.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_8 : adaptiveSpanEven115021_8.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_8 : adaptiveSpanWhole115021_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_8 : adaptiveSpanWhole115021_8.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_8 : adaptiveSpanWhole115021_8.spans = coreWholeSpans 0 adaptiveNumericSpans115021_8 := by
  decide +kernel
end Erdos883Verified

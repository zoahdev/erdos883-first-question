import Erdos883AdaptiveSpan115021Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_4 : adaptiveNumericSpans115021_4.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_4 : adaptiveSpanEven115021_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_4 : adaptiveSpanEven115021_4.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_4 : adaptiveSpanEven115021_4.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_4 : adaptiveSpanWhole115021_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_4 : adaptiveSpanWhole115021_4.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_4 : adaptiveSpanWhole115021_4.spans = coreWholeSpans 0 adaptiveNumericSpans115021_4 := by
  decide +kernel
end Erdos883Verified

import Erdos883AdaptiveSpan44342Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_4 : adaptiveNumericSpans44342_4.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_4 : adaptiveSpanEven44342_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_4 : adaptiveSpanEven44342_4.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_4 : adaptiveSpanEven44342_4.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_4 : adaptiveSpanWhole44342_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_4 : adaptiveSpanWhole44342_4.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_4 : adaptiveSpanWhole44342_4.spans = coreWholeSpans 0 adaptiveNumericSpans44342_4 := by
  decide +kernel
end Erdos883Verified
